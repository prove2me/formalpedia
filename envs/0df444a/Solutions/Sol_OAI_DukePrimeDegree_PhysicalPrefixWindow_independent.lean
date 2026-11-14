-- Prove2me | solution 1 for OAI.DukePrimeDegree.PhysicalPrefixWindow.independent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:55:16.589565+00:00
-- url     : https://prove2.me/submissions/d9d6a3f9-ac50-42d4-ad5e-5e7d88385d1e

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
import Mathlib.MeasureTheory.Constructions.Pi
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

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Product structure from equal normalized real conditionals

This is the finite-rectangle step of Einsiedler--Katok (2003), Lemma 8.2.
A common conditional measure, even if initially specified only up to a
scalar on each fiber, forces a genuine product measure after normalization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Equal normalized conditionals on the real factor force a product. -/
theorem eq_prod_of_constant_real_conditionals {B : Type*} [MeasurableSpace B]
    (μ : Measure (B × ℝ)) [IsFiniteMeasure μ]
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : ∀ᵐ x ∂μ.fst, μ.condKernel x = ν) :
    μ = μ.fst.prod ν := by
  have h' : μ.condKernel =ᵐ[μ.fst] Kernel.const B ν := h
  calc
    μ = μ.fst ⊗ₘ μ.condKernel := (Measure.disintegrate μ μ.condKernel).symm
    _ = μ.fst ⊗ₘ Kernel.const B ν := Measure.compProd_congr h'
    _ = μ.fst.prod ν := Measure.compProd_const

end DukePrimeDegree

end

end OAI
end

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
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RestrictedLeafProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product measures from projectively equal leaf restrictions -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma anchorNormalize_restrict_finite (ν : Measure ℝ) (J : Set ℝ) :
    IsFiniteMeasure ((anchorNormalize ν J).restrict J) := by
  constructor
  change ((ν J)⁻¹ • ν).restrict J univ < ∞
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Measure.smul_apply,smul_eq_mul]
  exact (ENNReal.inv_mul_le_one (ν J)).trans_lt ENNReal.one_lt_top

theorem restricted_eq_prod_of_projective_leaf_restrictions
    {B : Type*} [MeasurableSpace B] (μ : Measure (B × ℝ)) [IsFiniteMeasure μ]
    (J : Set ℝ) (hJ : MeasurableSet J) (leaf : B → Measure ℝ) (ν : Measure ℝ)
    (hres : ∀ᵐ w ∂μ.fst, (μ.condKernel w).restrict J = (leaf w).restrict J)
    (heq : ∀ᵐ w ∂μ.fst, anchorNormalize (leaf w) J = anchorNormalize ν J) :
    μ.restrict (univ ×ˢ J) = (μ.restrict (univ ×ˢ J)).fst.prod
      ((anchorNormalize ν J).restrict J) := by
  let : IsFiniteMeasure ((anchorNormalize ν J).restrict J) := anchorNormalize_restrict_finite ν J
  apply eq_prod_of_constant_real_conditionals
  have hbase : (μ.restrict (univ ×ˢ J)).fst ≪ μ.fst :=
    Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)
  have hcond := conditional_restrict_normalized μ (univ ×ˢ J) (MeasurableSet.univ.prod hJ)
  filter_upwards [hcond,hbase.ae_le hres,hbase.ae_le heq] with w hc hr he
  have hfiber : Prod.mk w ⁻¹' (univ ×ˢ J : Set (B × ℝ)) = J := by
    ext t
    simp
  rw [hfiber] at hc
  rw [hc.2]
  rw [←anchorNormalize_restrict_comm _ hJ subset_rfl,hr,
    anchorNormalize_restrict_comm _ hJ subset_rfl,he]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_NestedRealConditionals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.regularLeafKernel_sFinite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.intrinsicRootKernel_sFinite _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatibility of nested real conditional measures

Conditioning first on a transverse coordinate and then on all but one
leaf coordinate gives the same real conditional as conditioning on both
coordinates at once. This is the finite-chart form of
Einsiedler--Katok (2003), Lemma 8.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace DukePrimeDegree

variable {T : Type*} [MeasurableSpace T]
variable {B : Type*} [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]

theorem ae_nested_real_conditionals
    (μ : Measure (T × (B × ℝ))) [IsFiniteMeasure μ] :
    ∀ᵐ a ∂μ.fst, ∀ᵐ b ∂(μ.condKernel a).fst,
      (μ.map MeasurableEquiv.prodAssoc.symm).condKernel (a, b) =
        (μ.condKernel a).condKernel b := by
  let κ := μ.condKernel
  let ρ := μ.map MeasurableEquiv.prodAssoc.symm
  have hρ : ρ = (μ.fst ⊗ₘ κ.fst) ⊗ₘ κ.condKernel := by
    calc
      ρ = (μ.fst ⊗ₘ (κ.fst ⊗ₖ κ.condKernel)).map MeasurableEquiv.prodAssoc.symm := by
        rw [Kernel.disintegrate, Measure.disintegrate]
      _ = _ := Measure.compProd_assoc
  have hfst : ρ.fst = μ.fst ⊗ₘ κ.fst := by
    rw [hρ, Measure.fst_compProd]
  have heq : κ.condKernel =ᵐ[ρ.fst] ρ.condKernel :=
    eq_condKernel_of_measure_eq_compProd κ.condKernel (by rw [hfst]; exact hρ)
  rw [hfst] at heq
  have h := Measure.ae_ae_of_ae_compProd heq
  filter_upwards [h] with a ha
  have hinner := Kernel.condKernel_apply_eq_condKernel κ a
  filter_upwards [ha, hinner] with b hb hbc
  exact hb.symm.trans hbc

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_AmbientLeaves
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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



end RootBox



end PrimeDegreePackets


open scoped Topology ENNReal

open scoped Matrix Topology ENNReal ProbabilityTheory
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PositiveRootHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Holonomy across a positive-root pattern

A flow neutral on one root and contracting every other allowed matrix
entry sends every element of the pattern to its selected root entry.
The proved neutral holonomy theorem then identifies the actual leaves.
-/

noncomputable section
open Matrix MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

/-- One common null set controls all positive-pattern orbit pairs. This
is the leaf-constancy input for the root-product induction. -/
theorem exists_nullset_positiveRootPattern_holonomy
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2) {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ r, ell r = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ x ∉ N, ∀ y ∉ N, ∀ g : G (d + 1), PositiveRootPattern S g →
        rightAction x g = y → intrinsicRootLeaf hab μ y =
          basedRealMeasure (intrinsicRootLeaf hab μ x) (g.val a b) := by
  obtain ⟨N, hN, hN0, h⟩ := exists_nullset_neutral_root_holonomy d hab μ hA ell hell hneut
  refine ⟨N, hN, hN0, ?_⟩
  intro x hx y hy g hg hxy
  exact h x hx y hy g hxy _
    (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay g hg)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootFactorHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full holonomy in extremal-root product coordinates

The real quotient of a positive-root group records the displacement of
the selected intrinsic leaf even when both remaining and selected
coordinates change. This permits comparison at different good centers
in the disintegration step of EK2003, Proposition 8.3.
-/

noncomputable section
open Matrix MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_positiveRootGroup_holonomy
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (g₁ g₂ : positiveRootGeneratedGroup S),
        rightAction x g₁.val ∉ N → rightAction x g₂.val ∉ N →
        intrinsicRootLeaf hab μ (rightAction x g₂.val) =
          basedRealMeasure (intrinsicRootLeaf hab μ (rightAction x g₁.val))
            (g₂.val.val a b - g₁.val.val a b) := by
  obtain ⟨N, hN, hN0, hhol⟩ :=
    exists_nullset_positiveRootPattern_holonomy d S hpos hab ell hell hneut hdecay μ hA
  refine ⟨N, hN, hN0, ?_⟩
  intro x g₁ g₂ h₁ h₂
  let F := neutralRootEntryHom d S hpos hcomp hab ell hell hneut hdecay
  have hi : (g₁⁻¹).val.val a b = -g₁.val.val a b := by
    have H := congrArg Multiplicative.toAdd (map_inv F g₁)
    exact H
  have he : (g₁.val⁻¹ * g₂.val).val a b = g₂.val.val a b - g₁.val.val a b := by
    have H := congrArg Multiplicative.toAdd (F.map_mul g₁⁻¹ g₂)
    change (g₁.val⁻¹ * g₂.val).val a b = (g₁⁻¹).val.val a b + g₂.val.val a b at H
    rw [hi] at H
    exact H.trans (by ring)
  have hrel : rightAction (rightAction x g₁.val) (g₁.val⁻¹ * g₂.val) =
      rightAction x g₂.val := by
    rw [rightAction_mul]
    congr 1
    group
  simpa only [he] using hhol _ h₁ _ h₂ (g₁.val⁻¹ * g₂.val)
    (positiveRootGeneratedGroup_pattern S hcomp ((g₁⁻¹ * g₂).prop)) hrel

theorem exists_nullset_rootFactor_holonomy
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (w₁ w₂ : positiveRootGeneratedGroup (S.erase (a, b))) (t₁ t₂ : ℝ),
        rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection hab t₁) ∉ N →
        rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection hab t₂) ∉ N →
        intrinsicRootLeaf hab μ
            (rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection hab t₂)) =
          basedRealMeasure (intrinsicRootLeaf hab μ
            (rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection hab t₁))) (t₂ - t₁) := by
  obtain ⟨N, hN, hN0, hhol⟩ :=
    exists_nullset_positiveRootGroup_holonomy d S hpos hcomp hab ell hell hneut hdecay μ hA
  refine ⟨N, hN, hN0, ?_⟩
  intro x w₁ w₂ t₁ t₂ h₁ h₂
  let E := positiveRootRightFactorHomeomorph S hpos hcomp hab habS
    (erase_neutral_root_closed S hcomp (a, b) ell hneut hdecay)
  have he (w : positiveRootGeneratedGroup (S.erase (a, b))) (t : ℝ) :
      (E (w, t)).val.val a b = t :=
    congrArg Prod.snd (E.left_inv (w, t))
  have hE (w : positiveRootGeneratedGroup (S.erase (a, b))) (t : ℝ) :
      (E (w, t)).val = w.val * Matrix.SpecialLinearGroup.transvection hab t := rfl
  have H := hhol x (E (w₁, t₁)) (E (w₂, t₂)) h₁ h₂
  simp only [he] at H
  simpa only [hE] using H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ProjectiveLeafEquality
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the projective scalar after changing a leaf's origin -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem anchorNormalize_eq_of_basedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (J : Set ℝ) (t : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρt : 0 < ρ (Metric.ball t 1))
    (h : basedRealMeasure ν t = basedRealMeasure ρ t) :
    anchorNormalize ν J = anchorNormalize ρ J := by
  let e := Homeomorph.subRight t
  have H := congrArg (fun η : Measure ℝ => anchorNormalize η (e '' J)) h
  change anchorNormalize (anchorNormalize (centerRealMeasure ν t) (Metric.ball 0 1)) (e '' J) =
    anchorNormalize (anchorNormalize (centerRealMeasure ρ t) (Metric.ball 0 1)) (e '' J) at H
  rw [anchorNormalize_twice _ _ _
      (by rw [centerRealMeasure_ball]; exact hνt.ne')
      (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne),
    anchorNormalize_twice _ _ _
      (by rw [centerRealMeasure_ball]; exact hρt.ne')
      (by rw [centerRealMeasure_ball]; exact measure_ball_lt_top.ne)] at H
  change anchorNormalize (ν.map e.toMeasurableEquiv) (e.toMeasurableEquiv '' J) =
    anchorNormalize (ρ.map e.toMeasurableEquiv) (e.toMeasurableEquiv '' J) at H
  rw [anchorNormalize_map_equiv ν e.toMeasurableEquiv,
    anchorNormalize_map_equiv ρ e.toMeasurableEquiv] at H
  exact e.measurableEmbedding.map_injective H

theorem anchorNormalize_eq_of_rebasedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (J : Set ℝ) (t u : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρu : 0 < ρ (Metric.ball u 1))
    (h : basedRealMeasure ρ u = basedRealMeasure (basedRealMeasure ν t) (u-t)) :
    anchorNormalize ν J = anchorNormalize ρ J := by
  have he : basedRealMeasure ρ u = basedRealMeasure ν u := by
    simpa only [basedRealMeasure_rebase ν t (u-t) hνt, add_sub_cancel] using h
  have hνu : 0 < ν (Metric.ball u 1) := by
    by_contra hn
    have hz : ν (Metric.ball u 1) = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hb := congrArg (fun η : Measure ℝ => η (Metric.ball 0 1)) he
    rw [basedRealMeasure_ball_one ρ u hρu] at hb
    have hz' : basedRealMeasure ν u (Metric.ball 0 1) = 0 := by
      change (centerRealMeasure ν u (Metric.ball 0 1))⁻¹ *
        centerRealMeasure ν u (Metric.ball 0 1) = 0
      rw [centerRealMeasure_ball, hz, mul_zero]
    rw [hz'] at hb
    exact one_ne_zero hb
  exact anchorNormalize_eq_of_basedRealMeasure_eq ν ρ J u hνu hρu he.symm

lemma translatedRealMeasure_locallyFinite (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (a : ℝ) :
    IsLocallyFiniteMeasure (ν.map (Homeomorph.addRight a)) := by
  have he : (Homeomorph.addRight a : ℝ → ℝ) = Homeomorph.subRight (-a) := by
    funext x
    change x+a=x-(-a)
    ring
  rw [he]
  exact centerRealMeasure_locallyFinite ν (-a)

lemma translatedRealMeasure_ball (ν : Measure ℝ) (t a r : ℝ) :
    ν.map (Homeomorph.addRight a) (Metric.ball (t+a) r) = ν (Metric.ball t r) := by
  rw [←centerRealMeasure_ball, centerRealMeasure_translate, centerRealMeasure_ball]

theorem anchorNormalize_eq_of_shifted_rebasedRealMeasure_eq
    (ν ρ : Measure ℝ) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure ρ]
    (J : Set ℝ) (t u a b : ℝ)
    (hνt : 0 < ν (Metric.ball t 1)) (hρu : 0 < ρ (Metric.ball u 1))
    (h : basedRealMeasure ρ u = basedRealMeasure (basedRealMeasure ν t) ((u+b)-(t+a))) :
    anchorNormalize (ν.map (Homeomorph.addRight a)) J =
      anchorNormalize (ρ.map (Homeomorph.addRight b)) J := by
  let : IsLocallyFiniteMeasure (ν.map (Homeomorph.addRight a)) :=
    translatedRealMeasure_locallyFinite ν a
  let : IsLocallyFiniteMeasure (ρ.map (Homeomorph.addRight b)) :=
    translatedRealMeasure_locallyFinite ρ b
  apply anchorNormalize_eq_of_rebasedRealMeasure_eq _ _ J (t+a) (u+b)
  · rwa [translatedRealMeasure_ball]
  · rwa [translatedRealMeasure_ball]
  · simpa only [basedRealMeasure_translate] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.conditionalKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixBox.coordinateMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous holonomy for the full Gaussian root induction

One common null set controls every lexicographic elimination step. At
each step the remaining subgroup is normal and the selected root leaf
is constant along its cosets, with the exact root displacement retained.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

namespace InitialRootStep
variable {n : ℕ}

theorem exists_nullset_holonomy (d : ℕ) (s : InitialRootStep (d + 1))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (x : X (d + 1)) (w₁ w₂ : positiveRootGeneratedGroup (s.remaining.erase s.root))
        (t₁ t₂ : ℝ),
        rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁) ∉ N →
        rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂) ∉ N →
        intrinsicRootLeaf s.distinct μ
            (rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂)) =
          basedRealMeasure (intrinsicRootLeaf s.distinct μ
            (rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁))) (t₂-t₁) := by
  obtain ⟨ell,hell,hneut,hdecay⟩ := exists_lexicographic_root_weights d s.remaining
    s.positive s.remaining_positive s.least
  exact exists_nullset_rootFactor_holonomy d s.remaining s.remaining_positive s.remaining_closed
    s.distinct s.mem_remaining ell hell hneut hdecay μ hA

end InitialRootStep

theorem exists_nullset_all_initial_root_holonomy (d : ℕ)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d + 1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (s : InitialRootStep (d + 1)) (x : X (d + 1))
        (w₁ w₂ : positiveRootGeneratedGroup (s.remaining.erase s.root)) (t₁ t₂ : ℝ),
        rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁) ∉ N →
        rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂) ∉ N →
        intrinsicRootLeaf s.distinct μ
            (rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct t₂)) =
          basedRealMeasure (intrinsicRootLeaf s.distinct μ
            (rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct t₁))) (t₂-t₁) := by
  have : Countable (InitialRootStep (d + 1)) := inferInstanceAs
    (Countable {z : Finset (Fin (d+1) × Fin (d+1)) × (Fin (d+1) × Fin (d+1)) // _})
  choose N hNm hN0 hhol using fun s : InitialRootStep (d+1) => s.exists_nullset_holonomy d μ hA
  refine ⟨⋃ s, N s, MeasurableSet.iUnion hNm, measure_iUnion_null hN0, ?_⟩
  intro s x w₁ w₂ t₁ t₂ h₁ h₂
  exact hhol s x w₁ w₂ t₁ t₂
    (fun h => h₁ (mem_iUnion.mpr ⟨s,h⟩)) (fun h => h₂ (mem_iUnion.mpr ⟨s,h⟩))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ShiftedRootLeafHolonomy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projective root-leaf comparison with different coordinate origins -/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_nullset_shifted_initial_root_leaves (d : ℕ)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ N : Set (X (d+1)), MeasurableSet N ∧ μ N = 0 ∧
      ∀ (s : InitialRootStep (d+1)) (x : X (d+1))
        (w₁ w₂ : positiveRootGeneratedGroup (s.remaining.erase s.root))
        (t u a b : ℝ) (ν ρ : Measure ℝ),
        IsLocallyFiniteMeasure ν → IsLocallyFiniteMeasure ρ →
        0 < ν (Metric.ball t 1) → 0 < ρ (Metric.ball u 1) →
        let y₁ := rightAction x (w₁.val * Matrix.SpecialLinearGroup.transvection s.distinct (t+a))
        let y₂ := rightAction x (w₂.val * Matrix.SpecialLinearGroup.transvection s.distinct (u+b))
        y₁ ∉ N → y₂ ∉ N →
        intrinsicRootLeaf s.distinct μ y₁ = basedRealMeasure ν t →
        intrinsicRootLeaf s.distinct μ y₂ = basedRealMeasure ρ u →
        ∀ J : Set ℝ, anchorNormalize (ν.map (Homeomorph.addRight a)) J =
          anchorNormalize (ρ.map (Homeomorph.addRight b)) J := by
  obtain ⟨N,hN,hN0,hhol⟩ := exists_nullset_all_initial_root_holonomy d μ hA
  refine ⟨N,hN,hN0,?_⟩
  intro s x w₁ w₂ t u a b ν ρ hν hρ hνt hρu y₁ y₂ hy₁ hy₂ h₁ h₂ J
  let : IsLocallyFiniteMeasure ν := hν
  let : IsLocallyFiniteMeasure ρ := hρ
  have H := hhol s x w₁ w₂ (t+a) (u+b) hy₁ hy₂
  rw [h₁,h₂] at H
  exact anchorNormalize_eq_of_shifted_rebasedRealMeasure_eq ν ρ J t u a b hνt hρu H

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ShiftedFactorConditionals
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nested root conditionals when the time origin depends on the transversal -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

theorem factorChart_shifted_nested_conditionals {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1, z.2 + τ z.1))) :
    ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      A.conditionalKernel μ (e (s,w)) =
        ((σ.condKernel s).condKernel w).map (Homeomorph.addRight (τ (s,w))) := by
  let η := σ.map MeasurableEquiv.prodAssoc.symm
  have hm := conditional_map_fibers_embedding η e he
    (fun z => z.2 + τ z.1) (measurable_snd.add (hτ.comp measurable_fst))
  have hm' : ∀ᵐ z ∂η.fst,
      A.conditionalKernel μ (e z) = (η.condKernel z).map (Homeomorph.addRight (τ z)) := by
    filter_upwards [hm] with z hz
    change ((σ.map MeasurableEquiv.prodAssoc.symm).map
      (fun w => (e w.1,w.2 + τ w.1))).condKernel (e z) =
        (η.condKernel z).map (Homeomorph.addRight (τ z)) at hz
    simpa only [←hcoord, RootBox.conditionalKernel] using hz
  have hη : η = (σ.fst ⊗ₘ (σ.condKernel.fst ⊗ₖ σ.condKernel.condKernel)).map
      MeasurableEquiv.prodAssoc.symm := by
    rw [Kernel.disintegrate,Measure.disintegrate]
  have hf : η.fst = σ.fst ⊗ₘ σ.condKernel.fst := by
    rw [hη,Measure.compProd_assoc,Measure.fst_compProd]
  rw [hf] at hm'
  filter_upwards [Measure.ae_ae_of_ae_compProd hm', ae_nested_real_conditionals σ] with s hs hc
  filter_upwards [hs,hc] with w hw hcw
  rw [←hcw]
  exact hw

theorem factorChart_shifted_ae_nested {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2 + τ z.1)))
    {P : RootSlice a b k × ℝ → Prop} (hp : ∀ᵐ z ∂A.coordinateMeasure μ, P z) :
    ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      ∀ᵐ t ∂(σ.condKernel s).condKernel w, P (e (s,w),t + τ (s,w)) := by
  rw [hcoord] at hp
  have hm := (he.measurable.comp measurable_fst).prodMk
    (measurable_snd.add (hτ.comp measurable_fst))
  have h₁ := ae_of_ae_map hm.aemeasurable hp
  have h₂ := ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable h₁
  change ∀ᵐ z ∂σ, P (e (z.1,z.2.1),z.2.2 + τ (z.1,z.2.1)) at h₂
  have h₃ : ∀ᵐ z ∂σ.fst ⊗ₘ σ.condKernel, P (e (z.1,z.2.1),z.2.2 + τ (z.1,z.2.1)) := by
    simpa only [Measure.disintegrate] using h₂
  filter_upwards [Measure.ae_ae_of_ae_compProd h₃] with s hs
  have H : ∀ᵐ z ∂(σ.condKernel s).fst ⊗ₘ (σ.condKernel s).condKernel,
      P (e (s,z.1),z.2 + τ (s,z.1)) := by
    simpa only [Measure.disintegrate] using hs
  exact Measure.ae_ae_of_ae_compProd H

theorem shifted_leaf_restrict (ν κ : Measure ℝ) (V J : Set ℝ)
    (hJ : MeasurableSet J) (a : ℝ)
    (hJV : (Homeomorph.addRight a) '' J ⊆ V)
    (hκ : κ.map (Homeomorph.addRight a) = ν.restrict V) :
    (ν.map (Homeomorph.addRight a).symm).restrict J = κ.restrict J := by
  let f := Homeomorph.addRight a
  have he : κ = (ν.restrict V).map f.symm := by
    rw [←hκ,Measure.map_map f.symm.measurable f.measurable]
    have hid : f.symm ∘ f = id := by
      funext x
      exact f.symm_apply_apply x
    rw [hid,Measure.map_id]
  have hpre : f.symm ⁻¹' J ⊆ V := by
    intro x hx
    exact hJV ⟨f.symm x,hx,f.apply_symm_apply x⟩
  rw [he,Measure.restrict_map f.symm.measurable hJ,
    Measure.restrict_map f.symm.measurable hJ,
    Measure.restrict_restrict (f.symm.measurable hJ),inter_eq_left.mpr hpre]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ShiftedRootProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projective constancy of root factors in the remaining-group charts -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

theorem initialRootChart_shifted_leaves_constant
    (d : ℕ) (q : InitialRootStep (d+1)) {k : Fin (d+1)}
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice q.root.1 q.root.2 k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2 + τ z.1)))
    (base : T → X (d+1))
    (factor : B → positiveRootGeneratedGroup (q.remaining.erase q.root))
    (hparam : ∀ s w t, rootQuotientParametrization q.distinct (e (s,w),t) =
      rightAction (base s) ((factor w).val *
        Matrix.SpecialLinearGroup.transvection q.distinct (t - τ (s,w)))) :
    ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsLocallyFiniteMeasure ν ∧
      ∀ᵐ w ∂(σ.condKernel s).fst, ∀ J : Set ℝ,
        anchorNormalize ((A.leafMeasure R μ (e (s,w))).map
          (Homeomorph.addRight (-τ (s,w)))) J = anchorNormalize ν J := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx _ _ q.distinct
  obtain ⟨N,_hN,hN0,hhol⟩ := exists_nullset_shifted_initial_root_leaves d μ hA
  have havoid : ∀ᵐ x ∂μ, x ∉ N := by
    simpa only [ae_iff,not_not,ofPred_mem_eq] using hN0
  let F := A.leafMeasure R μ
  let P : RootSlice q.root.1 q.root.2 k × ℝ → Prop := fun z =>
    A.IsNormalizedRootLeaf R μ z.1 (F z.1) ∧
    0 < F z.1 (Metric.ball z.2 1) ∧
    intrinsicRootLeaf q.distinct μ (rootQuotientParametrization q.distinct z) =
      basedRealMeasure (F z.1) z.2 ∧
    rootQuotientParametrization q.distinct z ∉ N
  have hP : ∀ᵐ z ∂A.coordinateMeasure μ, P z := by
    have hs := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
    filter_upwards [hs,A.ae_leafMeasure_ball_pos R hAR μ hfree,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
      A.ae_coordinate_of_ambient μ havoid] with z hz hp hb hn
    exact ⟨hz,hp 1 zero_lt_one,hb,hn⟩
  filter_upwards [factorChart_shifted_ae_nested q.distinct A μ σ e he τ hτ hcoord hP] with s hs
  obtain ⟨w₀,hw₀⟩ := hs.exists
  obtain ⟨t₀,ht₀⟩ := hw₀.exists
  let ν := F (e (s,w₀))
  have hν : IsLocallyFiniteMeasure ν := ht₀.1.1
  let : IsLocallyFiniteMeasure ν := hν
  refine ⟨ν.map (Homeomorph.addRight (-τ (s,w₀))),
    translatedRealMeasure_locallyFinite ν _,?_⟩
  filter_upwards [hs] with w hw
  obtain ⟨t,ht⟩ := hw.exists
  let ρ := F (e (s,w))
  have hρ : IsLocallyFiniteMeasure ρ := ht.1.1
  have H := hhol q (base s) (factor w₀) (factor w)
    (t₀ + τ (s,w₀)) (t + τ (s,w)) (-τ (s,w₀)) (-τ (s,w)) ν ρ
    hν hρ ht₀.2.1 ht.2.1
  have hp₀ := ht₀.2.2.2
  have hp := ht.2.2.2
  have hb₀ := ht₀.2.2.1
  have hb := ht.2.2.1
  change rootQuotientParametrization q.distinct (e (s,w₀),t₀ + τ (s,w₀)) ∉ N at hp₀
  change rootQuotientParametrization q.distinct (e (s,w),t + τ (s,w)) ∉ N at hp
  change intrinsicRootLeaf q.distinct μ
    (rootQuotientParametrization q.distinct (e (s,w₀),t₀ + τ (s,w₀))) = _ at hb₀
  change intrinsicRootLeaf q.distinct μ
    (rootQuotientParametrization q.distinct (e (s,w),t + τ (s,w))) = _ at hb
  simp only [hparam,sub_eq_add_neg] at hp₀ hp hb₀ hb
  intro J
  exact (H hp₀ hp hb₀ hb J).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ShiftedRootConditionalProduct
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The remaining-root product law on physical time windows

The canonical one-root chart uses a time origin depending on all transverse
coordinates. Removing that origin before restricting gives the product step
in the ordered-root induction of EK2003, Proposition 8.3.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

theorem initialRootChart_shifted_conditional_product
    (d : ℕ) (q : InitialRootStep (d+1)) {k : Fin (d+1)}
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice q.root.1 q.root.2 k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2 + τ z.1)))
    (base : T → X (d+1))
    (factor : B → positiveRootGeneratedGroup (q.remaining.erase q.root))
    (hparam : ∀ s w t, rootQuotientParametrization q.distinct (e (s,w),t) =
      rightAction (base s) ((factor w).val *
        Matrix.SpecialLinearGroup.transvection q.distinct (t - τ (s,w))))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      (Homeomorph.addRight (τ (s,w))) '' J ⊆ A.time) :
    ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      (σ.condKernel s).restrict (univ ×ˢ J) =
        ((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx _ _ q.distinct
  have hnorm : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.IsNormalizedRootLeaf R μ z.1 (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
  have hs := factorChart_shifted_ae_nested q.distinct A μ σ e he τ hτ hcoord hnorm
  have hc := factorChart_shifted_nested_conditionals q.distinct A μ σ e he τ hτ hcoord
  have hp := initialRootChart_shifted_leaves_constant d q A R hAR μ hA σ e he τ hτ
    hcoord base factor hparam
  filter_upwards [hs,hc,hp,hwindow] with s hsn hsc hsp hsw
  obtain ⟨ν,_hν,heq⟩ := hsp
  refine ⟨(anchorNormalize ν J).restrict J,anchorNormalize_restrict_finite ν J,?_⟩
  apply restricted_eq_prod_of_projective_leaf_restrictions (σ.condKernel s) J hJ
    (fun w => (A.leafMeasure R μ (e (s,w))).map (Homeomorph.addRight (-τ (s,w)))) ν
  · filter_upwards [hsn,hsc,hsw] with w hwn hwc hww
    obtain ⟨t,ht⟩ := hwn.exists
    have hk : ((σ.condKernel s).condKernel w).map (Homeomorph.addRight (τ (s,w))) =
        (A.leafMeasure R μ (e (s,w))).restrict A.time :=
      hwc.symm.trans ht.2.2.1.symm
    have H := shifted_leaf_restrict (A.leafMeasure R μ (e (s,w)))
      ((σ.condKernel s).condKernel w) A.time J hJ (τ (s,w)) hww hk
    have hequiv : (Homeomorph.addRight (τ (s,w))).symm = Homeomorph.addRight (-τ (s,w)) := by
      ext x
      rfl
    rw [hequiv] at H
    exact H.symm
  · exact heq.mono fun _ hw => hw J

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_ShiftedRootPullback
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual coordinate measures for root charts with varying time origins -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]

lemma shiftedRootFactorPullback_map {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcover : A.transverse ⊆ Set.range e) :
    A.coordinateMeasure μ =
      ((shiftedRootFactorPullback hab A μ e τ).map MeasurableEquiv.prodAssoc.symm).map
        (shiftedRootFactorCoordinateMap e τ) := by
  have hf := shiftedRootFactorCoordinateMap_embedding e he τ hτ
  have hs : ∀ᵐ z ∂A.coordinateMeasure μ, z ∈ Set.range (shiftedRootFactorCoordinateMap e τ) := by
    filter_upwards [A.coordinateMeasure_ae_domain μ] with z hz
    obtain ⟨w,hw⟩ := hcover hz.1
    refine ⟨(w,z.2 - τ w),?_⟩
    apply Prod.ext hw
    dsimp [shiftedRootFactorCoordinateMap]
    ring
  unfold shiftedRootFactorPullback
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable MeasurableEquiv.prodAssoc.measurable]
  have hi : (MeasurableEquiv.prodAssoc.symm ∘ MeasurableEquiv.prodAssoc :
      ((T × B) × ℝ) → ((T × B) × ℝ)) = id := by
    funext z
    exact MeasurableEquiv.prodAssoc.symm_apply_apply z
  rw [hi,Measure.map_id,hf.map_comap]
  exact (Measure.restrict_eq_self_of_ae_mem hs).symm

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RemainingRootProductBoxes
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.exchangedRectangleMeasure_finite _root_.OAI.DukePrimeDegree.RootPrefixCoordinates.physicalPrefixMeasure_finite _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional local product boxes at every ordered-root step -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem remainingRootBox_conditional_product
    (d : ℕ) (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) [Nonempty Q.second]
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hcover : A.transverse ⊆ Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
    haveI := shiftedRootFactorPullback_finite q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
      (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      (σ.condKernel s).restrict (univ ×ˢ J) =
        ((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν := by
  intro σ
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  exact initialRootChart_shifted_conditional_product d q A R hAR μ hA σ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    (shiftedRootFactorPullback_map q.distinct A μ _
      (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding _
      (C.continuous_rectangleTime q g k Q).measurable hcover)
    (fun s => Quotient.mk _ ((g * s.val.1.val) * C.base s.val.2))
    (fun w => w.val) (C.rectangleSlice_orbit q g k Q) J hJ
      (Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun w => hwindow (s,w))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_ConditionalRectangleProducts
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseLocallyCompactSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized conditional products on actual rectangles -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma probability_eq_prod_marginals_of_prod
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure (A × B)) [IsProbabilityMeasure ρ]
    (ν : Measure A) (η : Measure B) [SFinite ν] [SFinite η]
    (h : ρ = ν.prod η) : ρ = ρ.fst.prod ρ.snd := by
  have hm : ν univ * η univ = 1 := by
    rw [←Measure.prod_prod,univ_prod_univ,←h,measure_univ]
  rw [h,Measure.fst,Measure.snd,Measure.map_fst_prod,Measure.map_snd_prod,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,mul_comm,hm,one_smul]

theorem conditional_restrict_rectangle_product
    {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
    [StandardBorelSpace B] [Nonempty B]
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hprod : ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      (σ.condKernel s).restrict (univ ×ˢ J) =
        ((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν) :
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
    ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  intro ρ
  have hbase : ρ.fst ≪ σ.fst :=
    Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)
  have hc := conditional_restrict_normalized σ (univ ×ˢ (univ ×ˢ J))
    (MeasurableSet.univ.prod (MeasurableSet.univ.prod hJ))
  filter_upwards [hc,hbase.ae_le hprod] with s hs hp
  have hfiber : Prod.mk s ⁻¹' (univ ×ˢ (univ ×ˢ J) : Set (T × (B × ℝ))) =
      univ ×ˢ J := by ext z; simp
  rw [hfiber] at hs
  obtain ⟨ν,hν,hp⟩ := hp
  let : IsFiniteMeasure ν := hν
  have he : ρ.condKernel s =
      ((σ.condKernel s) (univ ×ˢ J))⁻¹ •
        (((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν) := by
    calc
      _ = ((σ.condKernel s) (univ ×ˢ J))⁻¹ •
          ((σ.condKernel s).restrict (univ ×ˢ J)) := by
        rw [hs.2,anchorNormalize,Measure.restrict_smul]
      _ = _ := congrArg (fun θ : Measure (B × ℝ) =>
        ((σ.condKernel s) (univ ×ˢ J))⁻¹ • θ) hp
  rw [←Measure.prod_smul_left] at he
  exact probability_eq_prod_marginals_of_prod _ _ _ he

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_PhysicalPrefixWindows
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical product windows covering compact prefix-time sets -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

namespace PhysicalPrefixWindow
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*} [TopologicalSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}

variable [MeasurableSpace T] [BorelSpace T]

theorem independent_oai (B : PhysicalPrefixWindow q C g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    letI : Nonempty B.rectangle.second := B.second_nonempty.to_subtype
    haveI : StandardBorelSpace B.rectangle.second := B.rectangle.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct B.box μ
      (C.rectangleSlice q g B.pivot B.rectangle) (C.rectangleTime q g B.pivot B.rectangle)
    haveI := shiftedRootFactorPullback_finite q.distinct B.box μ
      (C.rectangleSlice q g B.pivot B.rectangle)
      (C.rectangleSlice_isOpenEmbedding q g B.pivot B.rectangle).measurableEmbedding
      (C.rectangleTime q g B.pivot B.rectangle)
      (C.continuous_rectangleTime q g B.pivot B.rectangle).measurable
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ B.interval))
    ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  let : Nonempty B.rectangle.second := B.second_nonempty.to_subtype
  let : StandardBorelSpace B.rectangle.second := B.rectangle.second_open.measurableSet.standardBorel
  intro σ
  let := shiftedRootFactorPullback_finite q.distinct B.box μ
    (C.rectangleSlice q g B.pivot B.rectangle)
    (C.rectangleSlice_isOpenEmbedding q g B.pivot B.rectangle).measurableEmbedding
    (C.rectangleTime q g B.pivot B.rectangle)
    (C.continuous_rectangleTime q g B.pivot B.rectangle).measurable
  apply conditional_restrict_rectangle_product σ B.interval B.interval_open.measurableSet
  exact remainingRootBox_conditional_product d q C g B.pivot B.rectangle B.box B.radius
    B.box_time_bound (by rw [B.transverse_eq]) B.interval B.interval_open.measurableSet
    B.window μ hA

end PhysicalPrefixWindow

end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DukePrimeDegree.PhysicalPrefixWindow.independent_oai.{u_1} := @OAI.DukePrimeDegree.PhysicalPrefixWindow.independent_oai.{u_1}
