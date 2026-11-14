-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:24:54.117297+00:00
-- url     : https://prove2.me/submissions/9a0917e0-0c44-4368-8e98-9bccc450a8ae

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
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
import Definitions.Def_OAIQ244Duke022
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma matrixBall_isOpen (n : ℕ) (r : ℝ) : IsOpen (matrixBall n r) := by
  simp only [matrixBall, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt _ continuous_const
  exact ((continuous_apply j).comp ((continuous_apply i).comp Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)).sub
    continuous_const |>.abs

open scoped Matrix
open Matrix

open TopologicalSpace
open scoped Topology

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_InverseEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk
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
namespace PrimeDegreePackets

lemma one_mem_matrixBall (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 : G n) ∈ matrixBall n r := by
  intro i j
  simpa using hr

lemma matrixBall_nhds_basis {n : ℕ} {U : Set (G n)} (hU : U ∈ 𝓝 (1 : G n)) :
    ∃ r : ℝ, 0 < r ∧ matrixBall n r ⊆ U := by
  have hv : Topology.IsInducing (fun g : G n => g.1) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing
  rw [hv.nhds_eq_comap] at hU
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r,hr,fun g hg => hVU (hsub ?_)⟩
  change dist g.1 (1 : G n).1 < r
  rw [dist_eq_norm]
  exact (Matrix.norm_lt_iff hr).mpr hg

 

lemma local_uniform_chart_injective {n : ℕ} (x : X n) :
    ∃ U : Set (X n), IsOpen U ∧ x ∈ U ∧ ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ U, Set.InjOn (fun g => rightAction y g) (matrixBall n r) := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨V,hVo,hgV,hVi⟩ :=
      (quotient_covering n).isLocalHomeomorph.isLocallyInjective g
    have hpre : (fun u : G n => g*u) ⁻¹' V ∈ 𝓝 (1 : G n) := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      simpa using hVo.mem_nhds hgV
    obtain ⟨W,hWo,h1W,hWW⟩ := exists_open_nhds_one_mul_subset hpre
    obtain ⟨r,hr,hrW⟩ := matrixBall_nhds_basis (hWo.mem_nhds h1W)
    refine ⟨(fun u => Quotient.mk _ (g*u)) '' W, ?_, ?_, r,hr,?_⟩
    · rw [← Set.image_image]
      exact (quotient_covering n).isOpenMap _ ((Homeomorph.mulLeft g).isOpenMap _ hWo)
    · exact ⟨1,h1W,by simp⟩
    · rintro y ⟨u,hu,rfl⟩ v hv w hw heq
      have hgv : g*(u*v) ∈ V := hWW (Set.mul_mem_mul hu (hrW hv))
      have hgw : g*(u*w) ∈ V := hWW (Set.mul_mem_mul hu (hrW hw))
      have He : g*(u*v) = g*(u*w) := hVi hgv hgw (by
        change Quotient.mk _ ((g*u)*v) = Quotient.mk _ ((g*u)*w) at heq
        simpa only [mul_assoc] using heq)
      exact mul_left_cancel (mul_left_cancel He)


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
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
namespace PrimeDegreePackets

 

theorem fixedPoint_mem_closed_convex_orbit {H E : Type*} [Monoid H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : H → E →ₗᵢ[ℝ] E) (hU : ∀ g h x, U g (U h x) = U (g*h) x)
    (x : E) : ∃ v : E, v ∈ closure (convexHull ℝ (Set.range (fun g => U g x))) ∧
      ∀ g, U g v = v := by
  let O := Set.range (fun g => U g x)
  let C := closure (convexHull ℝ O)
  have hconv : Convex ℝ C := (convex_convexHull ℝ O).closure
  have hnon : C.Nonempty := ⟨U 1 x,subset_closure (subset_convexHull ℝ O ⟨1,rfl⟩)⟩
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hnon
    isClosed_closure.isComplete hconv (0:E)
  refine ⟨v,hv,?_⟩
  intro g
  have himage : U g '' C ⊆ C := by
    calc
      U g '' C ⊆ closure (U g '' convexHull ℝ O) :=
        image_closure_subset_closure_image (U g).continuous
      _ = closure (convexHull ℝ (U g '' O)) := by
        exact congrArg closure ((U g).toLinearMap.image_convexHull O)
      _ ⊆ C := closure_mono (convexHull_mono ?_)
    rintro _ ⟨_,⟨h,rfl⟩,rfl⟩
    exact ⟨g*h,(hU g h x).symm⟩
  have hg : U g v ∈ C := himage ⟨v,hv,rfl⟩
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin (U g v) hg
  have hn := norm_sub_sq_real (U g v) v
  have hh : inner ℝ v (U g v) = inner ℝ (U g v) v := real_inner_comm _ _
  simp only [zero_sub,inner_neg_left,inner_sub_right,real_inner_self_eq_norm_sq] at hinner
  rw [(U g).norm_map] at hn
  have he : ‖U g v-v‖^2 = 0 := by nlinarith [sq_nonneg ‖U g v-v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))



end PrimeDegreePackets

open scoped Classical
namespace PrimeDegreePackets


lemma measurable_actionInvariantSigma {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] {f : Y → ℝ} (hf : Measurable f)
    (hinv : ∀ (g : H) (y : Y), f (g • y) = f y) : Measurable[actionInvariantSigma H Y] f := by
  intro s hs
  rw [actionInvariantSigma,MeasurableSpace.measurableSet_iInf]
  intro g
  refine ⟨hf hs,?_⟩
  ext y
  simp only [Set.mem_preimage,hinv]

 

theorem exists_pointwise_invariant_representative {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [MeasurableSpace Y] (μ : Measure Y)
    (hm : ∀ g : H, Measurable (fun y : Y => g • y))
    (f : Y → ℝ) (hf : Measurable f)
    (hinv : ∀ g : H, (fun y => f (g • y)) =ᵐ[μ] f) :
    ∃ f₀ : Y → ℝ, Measurable[actionInvariantSigma H Y] f₀ ∧ f₀ =ᵐ[μ] f ∧
      ∀ (g : H) (y : Y), f₀ (g • y) = f₀ y := by
  let A : Set Y := {y | ∀ g : H, f (g • y) = f y}
  have hA : MeasurableSet A := by
    simpa only [A,Set.ofPred_forall,Function.comp_apply] using
      MeasurableSet.iInter (fun g => measurableSet_eq_fun (hf.comp (hm g)) hf)
  have hconull : ∀ᵐ y ∂μ, y ∈ A := ae_all_iff.mpr hinv
  have hstable (g : H) (y : Y) : g • y ∈ A ↔ y ∈ A := by
    constructor
    · intro hy h
      have hfgy : f y = f (g • y) := by simpa only [inv_smul_smul] using hy g⁻¹
      have hh := hy (h*g⁻¹)
      simpa only [mul_smul,inv_smul_smul,hfgy] using hh
    · intro hy h
      simpa only [mul_smul,hy g] using hy (h*g)
  let f₀ := A.indicator f
  have hmeas : Measurable f₀ := hf.indicator hA
  have hfixed (g : H) (y : Y) : f₀ (g • y) = f₀ y := by
    by_cases hy : y ∈ A
    · simp only [f₀,Set.indicator_of_mem hy,Set.indicator_of_mem ((hstable g y).mpr hy)]
      exact hy g
    · simp only [f₀,Set.indicator_of_notMem hy,
        Set.indicator_of_notMem (not_imp_not.mpr (hstable g y).mp hy)]
  refine ⟨f₀,measurable_actionInvariantSigma hmeas hfixed,?_,hfixed⟩
  filter_upwards [hconull] with y hy
  exact Set.indicator_of_mem hy f

end PrimeDegreePackets

open scoped Topology ENNReal Classical
namespace PrimeDegreePackets


lemma orbitConvexHull_measurable {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (hm : ∀ g : H, Measurable (fun y : Y => g • y))
    {f F : Y → ℝ} (hf : Measurable f) (hF : F ∈ orbitConvexHull (H := H) f) :
    Measurable F := by
  have hc : Convex ℝ {F : Y → ℝ | Measurable F} := by
    intro F hF G hG a b _ _ _
    exact (hF.const_smul a).add (hG.const_smul b)
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩
  exact hf.comp (hm g)

lemma orbitConvexHull_interval {H Y : Type*} [Group H] [MulAction H Y]
    {f F : Y → ℝ} {a b : ℝ} (hf : ∀ y, f y ∈ Set.Icc a b)
    (hF : F ∈ orbitConvexHull (H := H) f) : ∀ y, F y ∈ Set.Icc a b := by
  have hc : Convex ℝ {F : Y → ℝ | ∀ y, F y ∈ Set.Icc a b} := by
    intro F hF G hG c d hc hd hcd y
    exact (convex_Icc a b) (hF y) (hG y) hc hd hcd
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩ y
  exact hf (g • y)

 

lemma orbitConvexHull_integral {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {f F : Y → ℝ} (hf : Integrable f ν) (hF : F ∈ orbitConvexHull (H := H) f) :
    Integrable F ν ∧ (∫ y, F y ∂ν) = ∫ y, f y ∂ν := by
  let : MeasurableConstSMul H Y := ⟨fun g => (hp g).measurable⟩
  have hc : Convex ℝ {F : Y → ℝ | Integrable F ν ∧ (∫ y, F y ∂ν) = ∫ y, f y ∂ν} := by
    intro F hF G hG a b _ _ hab
    refine ⟨(hF.1.smul a).add (hG.1.smul b),?_⟩
    change (∫ y, a * F y+b * G y ∂ν) = _
    rw [integral_add (hF.1.const_mul a) (hG.1.const_mul b),
      integral_const_mul,integral_const_mul,hF.2,hG.2]
    rw [← add_mul,hab,one_mul]
  apply convexHull_min ?_ hc hF
  rintro _ ⟨g,rfl⟩
  exact ⟨(hp g).integrable_comp_of_integrable hf,
    (hp g).integral_comp (MeasurableEquiv.smul g).measurableEmbedding f⟩

end PrimeDegreePackets


namespace PrimeDegreePackets

 
lemma lp_convex_orbit_representative {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (μ : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ)
    {f : Y → ℝ} (hf : MemLp f 2 μ) {z : Lp ℝ 2 μ}
    (hz : z ∈ convexHull ℝ (Set.range fun g : H =>
      Lp.compMeasurePreservingₗᵢ ℝ (fun y : Y => g⁻¹ • y) (hp g⁻¹) (hf.toLp f))) :
    ∃ F ∈ orbitConvexHull (H := H) f, z =ᵐ[μ] F := by
  let C : Set (Lp ℝ 2 μ) := {z | ∃ F ∈ orbitConvexHull (H := H) f, z =ᵐ[μ] F}
  have hconv : Convex ℝ C := by
    intro z hz w hw a b ha hb hab
    obtain ⟨F,hF,hzF⟩ := hz
    obtain ⟨G,hG,hwG⟩ := hw
    refine ⟨a • F+b • G, (convex_convexHull ℝ _) hF hG ha hb hab,?_⟩
    filter_upwards [Lp.coeFn_add (a • z) (b • w),Lp.coeFn_smul a z,
      Lp.coeFn_smul b w,hzF,hwG] with y hy ha' hb' hz' hw'
    simp only [hy,ha',hb',Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz',hw']
  apply convexHull_min ?_ hconv hz
  rintro _ ⟨g,rfl⟩
  refine ⟨fun y => f (g⁻¹ • y),subset_convexHull ℝ _ ⟨g⁻¹,rfl⟩,?_⟩
  exact (Lp.coeFn_compMeasurePreserving (hf.toLp f) (hp g⁻¹)).trans
    ((hp g⁻¹).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)

 

theorem exists_invariant_orbit_average_limit {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [MeasurableSpace Y] (μ : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ)
    {f : Y → ℝ} (hf : MemLp f 2 μ) :
    ∃ v : Y → ℝ, Measurable[actionInvariantSigma H Y] v ∧
      (∀ (g : H) (y : Y), v (g • y) = v y) ∧
      ∃ F : ℕ → Y → ℝ, (∀ k, F k ∈ orbitConvexHull (H := H) f) ∧
        ∀ᵐ y ∂μ, Tendsto (fun k => F k y) atTop (𝓝 (v y)) := by
  let U : H → (Lp ℝ 2 μ) →ₗᵢ[ℝ] (Lp ℝ 2 μ) := fun g =>
    Lp.compMeasurePreservingₗᵢ ℝ (fun y : Y => g⁻¹ • y) (hp g⁻¹)
  have hU (g h : H) (x : Lp ℝ 2 μ) : U g (U h x) = U (g*h) x := by
    change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ x) =
      Lp.compMeasurePreserving (fun y : Y => (g*h)⁻¹ • y) (hp (g*h)⁻¹) x
    rw [← Lp.compMeasurePreserving_comp_apply]
    simp only [Function.comp_def,_root_.mul_inv_rev,mul_smul]
  obtain ⟨v,hv,hfix⟩ := fixedPoint_mem_closed_convex_orbit U hU (hf.toLp f)
  have hvfix (g : H) : (fun y => v (g • y)) =ᵐ[μ] v := by
    have H := Lp.coeFn_compMeasurePreserving v (hp g)
    have he : Lp.compMeasurePreserving (fun y : Y => g • y) (hp g) v = v := by
      have he := hfix g⁻¹
      change Lp.compMeasurePreserving (fun y : Y => (g⁻¹)⁻¹ • y) _ v = v at he
      simpa only [inv_inv] using he
    simpa only [he,Function.comp_def] using H.symm
  obtain ⟨v₀,hv₀,hveq,hvfix₀⟩ := exists_pointwise_invariant_representative μ
    (fun g => (hp g).measurable) v (Lp.stronglyMeasurable v).measurable hvfix
  obtain ⟨z,hz,hzlim⟩ := mem_closure_iff_seq_limit.mp hv
  choose F hF hzF using fun k => lp_convex_orbit_representative μ hp hf (hz k)
  obtain ⟨ns,-,hns⟩ := (tendstoInMeasure_of_tendsto_Lp hzlim).exists_seq_tendsto_ae
  refine ⟨v₀,hv₀,hvfix₀,F ∘ ns,fun k => hF (ns k),?_⟩
  filter_upwards [hns,hveq,ae_all_iff.mpr hzF] with y hy hvy hzy
  simpa only [Function.comp_apply,hzy,hvy] using hy

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma orbitConvexHull_aeSetIntegral {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y)
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {S : Set Y} (hS : MeasurableSet S)
    (hSfix : ∀ g : H, (fun y : Y => g • y) ⁻¹' S =ᵐ[ν] S)
    {f F : Y → ℝ} (hf : Integrable f ν) (hF : F ∈ orbitConvexHull (H := H) f) :
    (∫ y in S, F y ∂ν) = ∫ y in S, f y ∂ν := by
  apply (orbitConvexHull_integral (ν.restrict S) (fun g => ?_) hf.integrableOn hF).2
  have hg := (hp g).restrict_preimage hS
  simpa only [Measure.restrict_congr_set (hSfix g)] using hg

 

lemma invariant_set_independent_of_orbit_indicator_limit {H Y : Type*} [Group H] [MulAction H Y]
    [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    {B : Set Y} (hB : MeasurableSet B) {F : ℕ → Y → ℝ}
    (hF : ∀ k, F k ∈ orbitConvexHull (H := H) (B.indicator (fun _ => (1:ℝ))))
    {c : ℝ} (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => F k y) atTop (𝓝 c))
    {S : Set Y} (hS : MeasurableSet S)
    (hSfix : ∀ g : H, (fun y : Y => g • y) ⁻¹' S =ᵐ[ν] S) :
    ν.real (B ∩ S) = ν.real S * ν.real B := by
  have hbmeas : Measurable (B.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hB
  have hbint : Integrable (B.indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator hB
  have hfm (k : ℕ) : Measurable (F k) :=
    orbitConvexHull_measurable (fun g => (hp g).measurable) hbmeas (hF k)
  have hbnd (k : ℕ) (y : Y) : ‖F k y‖ ≤ 1 := by
    have hb : ∀ y : Y, B.indicator (fun _ => (1:ℝ)) y ∈ Icc (0:ℝ) 1 := by
      intro y
      by_cases hy : y ∈ B <;> simp [hy]
    have hx := orbitConvexHull_interval hb (hF k) y
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hc : ν.real B = c := by
    have H := tendsto_integral_of_dominated_convergence (fun _ : Y => (1:ℝ))
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ (hbnd k)) hlim
    have hi (k : ℕ) : (∫ y, F k y ∂ν) = ν.real B := by
      rw [(orbitConvexHull_integral ν hp hbint (hF k)).2,integral_indicator hB]
      simp [integral_const,Measure.real]
    simp only [hi,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at H
    exact tendsto_nhds_unique tendsto_const_nhds H
  have H := tendsto_integral_of_dominated_convergence (μ := ν.restrict S)
    (fun _ : Y => (1:ℝ))
    (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
    (fun k => ae_of_all _ (hbnd k)) (ae_restrict_of_ae hlim)
  have hi (k : ℕ) : (∫ y in S, F k y ∂ν) = ν.real (B ∩ S) := by
    rw [orbitConvexHull_aeSetIntegral ν hp hS hSfix hbint (hF k),integral_indicator hB]
    simp [integral_const,Measure.real,Measure.restrict_apply hB]
  simp only [hi,integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at H
  rw [← hc] at H
  exact tendsto_nhds_unique tendsto_const_nhds H

 

theorem ergodicSMul_of_orbit_indicator_limits {H Y : Type*} [Group H] [MulAction H Y]
    [mY : MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) ν ν)
    (C : Set (Set Y)) (hgen : mY = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (havg : ∀ B ∈ C, ∃ c : ℝ, ∃ F : ℕ → Y → ℝ,
      (∀ k, F k ∈ orbitConvexHull (H := H) (B.indicator (fun _ => (1:ℝ)))) ∧
        ∀ᵐ y ∂ν, Tendsto (fun k => F k y) atTop (𝓝 c)) :
    ErgodicSMul H Y ν := by
  refine { measure_preimage_smul := fun g _ hs => (hp g).measure_preimage hs.nullMeasurableSet
           aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  intro S hS hSfix
  have hmeas (B : Set Y) (hB : B ∈ C) : MeasurableSet B := by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hB
  have hind (B : Set Y) (hB : B ∈ C) : ν.real (B ∩ S) = ν.real S * ν.real B := by
    obtain ⟨c,F,hF,hlim⟩ := havg B hB
    exact invariant_set_independent_of_orbit_indicator_limit ν hp (hmeas B hB)
      hF hlim hS hSfix
  have he : ν.restrict S = (ν S) • ν := by
    apply ext_of_generate_finite C hgen hpi
    · intro B hB
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ?_).mp
      · simpa only [Measure.real,Measure.restrict_apply (hmeas B hB),
          Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul] using hind B hB
      · simp only [Measure.smul_apply,smul_eq_mul]
        exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
    · simp
  have hreal := congrArg (fun η : Measure Y => η.real S) he
  simp only [Measure.real,Measure.restrict_apply hS,inter_self,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul] at hreal
  have hz : (ν S).toReal * ((ν S).toReal - 1) = 0 := by nlinarith [hreal]
  rw [eventuallyConst_set]
  rcases mul_eq_zero.mp hz with hz | hz
  · right
    apply measure_eq_zero_iff_ae_notMem.mp
    exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)
  · left
    have hmass : ν S = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
      simpa only [ENNReal.toReal_one] using sub_eq_zero.mp hz
    have hcompl : ν Sᶜ = 0 := by rw [measure_compl hS (measure_ne_top _ _),hmass,measure_univ,tsub_self]
    exact (measure_eq_zero_iff_ae_notMem.mp hcompl).mono fun y hy => not_not.mp hy

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ErgodicDecomposition
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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
namespace PrimeDegreePackets

 

theorem condExpKernel_invariant {Y : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hm : m ≤ mY) {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (hfix : m ≤ MeasurableSpace.invariants T) :
    ∀ᵐ x ∂μ.trim hm, Measure.map T (condExpKernel μ m x) = condExpKernel μ m x := by
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdiag : τ ⊗ₘ κ = @Measure.map Y (Y × Y) mY (m.prod mY) Function.diag μ :=
    compProd_trim_condExpKernel hm
  have hprod : τ ⊗ₘ κ.map T = τ ⊗ₘ κ := by
    rw [Measure.compProd_map hT.measurable, hdiag]
    apply Measure.ext_prod
    intro A B hA hB
    have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
      (measurable_id'' hm).prodMk measurable_id
    rw [Measure.map_apply (measurable_id.prodMap hT.measurable) (hA.prod hB),
      Measure.map_apply hδ
        ((measurable_id.prodMap hT.measurable) (hA.prod hB)),
      Measure.map_apply hδ (hA.prod hB)]
    change μ (A ∩ T ⁻¹' B) = μ (A ∩ B)
    conv_lhs => rw [← (hfix _ hA).2, ← Set.preimage_inter]
    exact hT.measure_preimage ((hm _ hA |>.inter hB).nullMeasurableSet)
  let : IsMarkovKernel (κ.map T) := Kernel.IsMarkovKernel.map κ hT.measurable
  have H₁ := condKernel_compProd τ (κ.map T)
  have H₂ := condKernel_compProd τ κ
  have H₁' : (τ ⊗ₘ κ).condKernel =ᵐ[τ] κ.map T := by
    simpa only [hprod] using H₁
  have H := H₁'.symm.trans H₂
  filter_upwards [H] with x hx
  change (κ.map T) x = κ x at hx
  simpa only [Kernel.map_apply _ hT.measurable] using hx

 

theorem invariant_kernel_decomposition {Y I : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] [Countable I]
    (μ : Measure Y) [IsProbabilityMeasure μ] (T : I → Y → Y)
    (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hm : m ≤ mY)
    (hfix : ∀ i, m ≤ MeasurableSpace.invariants (T i)) :
    condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
      ∀ᵐ x ∂μ.trim hm, ∀ i, Measure.map (T i) (condExpKernel μ m x) =
        condExpKernel μ m x := by
  exact ⟨condExpKernel_comp_trim hm, ae_all_iff.mpr
    (fun i => condExpKernel_invariant m μ hm (hT i) (hfix i))⟩

 

theorem condExpKernel_ae_constant {Y : Type*} (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hm : m ≤ mY) {f : Y → ℝ} (hf : Measurable[m] f) :
    ∀ᵐ x ∂μ.trim hm, ∀ᵐ y ∂condExpKernel μ m x, f y = f x := by
  have hfull : Measurable f := hf.mono hm le_rfl
  have hset : @MeasurableSet (Y × Y) (m.prod mY) {p | f p.2 = f p.1} :=
    measurableSet_eq_fun (hfull.comp measurable_snd) (hf.comp measurable_fst)
  let : MeasurableSpace (Y × Y) := m.prod mY
  apply (Measure.ae_compProd_iff hset).mp
  rw [compProd_trim_condExpKernel hm]
  have hδ : @Measurable Y (Y × Y) mY (m.prod mY) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  exact (@ae_map_iff Y (Y × Y) mY (m.prod mY) μ Function.diag
    hδ.aemeasurable (fun p => f p.2 = f p.1) hset).mpr
      (Eventually.of_forall fun _ => rfl)

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem action_ergodic_decomposition {H Y : Type*} [Group H] [Countable H]
    [MulAction H Y] [mY : MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (hp : ∀ g : H, MeasurePreserving (fun y : Y => g • y) μ μ) :
    condExpKernel μ (actionInvariantSigma H Y) ∘ₘ
      μ.trim (actionInvariantSigma_le H Y) = μ ∧
      ∀ᵐ x ∂μ.trim (actionInvariantSigma_le H Y),
        ErgodicSMul H Y (condExpKernel μ (actionInvariantSigma H Y) x) := by
  let m := actionInvariantSigma H Y
  let : MeasurableSpace Y := mY
  let hm := actionInvariantSigma_le H Y
  let κ := condExpKernel μ m
  let τ := μ.trim hm
  have hdec := invariant_kernel_decomposition m μ (fun g : H => fun y : Y => g • y)
    hp hm (fun g => iInf_le _ g)
  refine ⟨hdec.1,?_⟩
  let C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet Y)
  have hCcount : C.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  have hCgen : mY = MeasurableSpace.generateFrom C := by
    simp only [C,generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
    rfl
  have hCpi : IsPiSystem C := fun _ hA _ hB _ =>
    isSetAlgebra_generateSetAlgebra.inter_mem hA hB
  have hCm (B : C) : MeasurableSet (B : Set Y) := by
    change @MeasurableSet Y mY _
    rw [hCgen]
    exact MeasurableSpace.measurableSet_generateFrom B.property
  let : Countable C := hCcount.to_subtype
  have hAv (B : C) := exists_invariant_orbit_average_limit μ hp
    ((memLp_const (1:ℝ)).indicator (hCm B) :
      MemLp ((B:Set Y).indicator (fun _ => (1:ℝ))) 2 μ)
  choose v hv hvfix F hF hlim using hAv
  have hlimfiber (B : C) : ∀ᵐ x ∂τ, ∀ᵐ y ∂κ x,
      Tendsto (fun k => F B k y) atTop (𝓝 (v B y)) := by
    apply Measure.ae_ae_of_ae_comp
    change ∀ᵐ y ∂κ ∘ₘ τ, Tendsto (fun k => F B k y) atTop (𝓝 (v B y))
    rw [show κ ∘ₘ τ = μ from hdec.1]
    exact hlim B
  have hconst (B : C) : ∀ᵐ x ∂τ, ∀ᵐ y ∂κ x, v B y = v B x :=
    condExpKernel_ae_constant m μ hm (hv B)
  filter_upwards [hdec.2,ae_all_iff.mpr hlimfiber,ae_all_iff.mpr hconst]
    with x hx hxl hxc
  have hpx (g : H) : MeasurePreserving (fun y : Y => g • y) (κ x) (κ x) :=
    ⟨(hp g).measurable,hx g⟩
  apply ergodicSMul_of_orbit_indicator_limits (κ x) hpx C hCgen hCpi
  intro B hB
  refine ⟨v ⟨B,hB⟩ x,F ⟨B,hB⟩,hF ⟨B,hB⟩,?_⟩
  filter_upwards [hxl ⟨B,hB⟩,hxc ⟨B,hB⟩] with y hy hyc
  simpa only [hyc] using hy

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem preserving_of_dense_action {G H Y : Type*} [Group G] [Group H]
    [TopologicalSpace G] [FirstCountableTopology G] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [HasOuterApproxClosed Y] [MulAction G Y] [ContinuousSMul G Y]
    («φ» : H →* G) (hdense : DenseRange «φ») (ν : Measure Y) [IsProbabilityMeasure ν]
    (hp : ∀ h : H, MeasurePreserving (fun y : Y => «φ» h • y) ν ν) (g : G) :
    MeasurePreserving (fun y : Y => g • y) ν ν := by
  refine ⟨(continuous_const_smul g).measurable,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (continuous_const_smul g).measurable.aemeasurable f.continuous.aestronglyMeasurable]
  have hcont : Continuous (fun a : G => ∫ y, f (a • y) ∂ν) :=
    continuous_of_dominated
      (fun a => (f.continuous.comp (continuous_const_smul a)).aestronglyMeasurable)
      (fun a => ae_of_all _ (fun y => f.norm_coe_le_norm (a • y)))
      (integrable_const ‖f‖)
      (ae_of_all _ (fun y => f.continuous.comp (continuous_id.smul continuous_const)))
  refine hdense.induction_on (p := fun a : G => (∫ y, f (a • y) ∂ν) = ∫ y, f y ∂ν)
    g (isClosed_eq hcont continuous_const) ?_
  intro h
  rw [← integral_map (hp h).measurable.aemeasurable f.continuous.aestronglyMeasurable,
    (hp h).map_eq]

end PrimeDegreePackets


open MeasureTheory Set Topology UniformSpace TopologicalSpace

open scoped ENNReal Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RepeatedRoot
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The algebraic obstruction to exceptional returns

EKL (Annals of Mathematics 164 (2006), Proposition 5.2) excludes an
integral special-linear matrix with exactly one repeated eigenvalue and
no eigenvalues equal to ±1. The first step is that a unique repeated
root of a rational polynomial must be rational: a distinct Galois
conjugate would also be a common root of the polynomial and its derivative.
-/

noncomputable section
open Polynomial
open scoped Classical

namespace DukePrimeDegree

theorem unique_common_root_is_rational
    (p : ℚ[X]) (hp : p ≠ 0) (x : ℂ)
    (hx : aeval x p = 0) (hdx : aeval x p.derivative = 0)
    (hunique : ∀ y : ℂ, aeval y p = 0 → aeval y p.derivative = 0 → y = x) :
    ∃ q : ℚ, (q : ℂ) = x := by
  have hi : IsIntegral ℚ x := (show IsAlgebraic ℚ x from ⟨p, hp, hx⟩).isIntegral
  have hs : IsSeparable ℚ x := (minpoly.irreducible hi).separable
  have hmem : x ∈ (⊥ : Subalgebra ℚ ℂ) := by
    by_contra hn
    obtain ⟨y, hxy, hconj⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot hs (IsAlgClosed.splits _)).mp hn
    have hpy : minpoly ℚ y ∣ p := by
      rw [← hconj]
      exact minpoly.dvd ℚ x hx
    have hdpy : minpoly ℚ y ∣ p.derivative := by
      rw [← hconj]
      exact minpoly.dvd ℚ x hdx
    exact hxy (hunique y (minpoly.dvd_iff.mp hpy) (minpoly.dvd_iff.mp hdpy)).symm
  exact Algebra.mem_bot.mp hmem

theorem rational_root_of_monic_unit_constant
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0))
    {q : ℚ} (hq : aeval q p = 0) : q = 1 ∨ q = -1 := by
  obtain ⟨a, hqa, ha⟩ := exists_integer_of_is_root_of_monic hp hq
  have hu : IsUnit a := isUnit_of_dvd_unit ha hc
  have habs : |a| = 1 := Int.isUnit_iff_abs_eq.mp hu
  rcases le_total 0 a with hnonneg | hnonpos
  · left
    rw [abs_of_nonneg hnonneg] at habs
    simpa only [habs, map_one] using hqa
  · right
    rw [abs_of_nonpos hnonpos] at habs
    have ha : a = -1 := by omega
    simpa only [ha, map_neg, map_one] using hqa

/-- The repeated-root obstruction in EKL Proposition 5.2, in polynomial form. -/
theorem unique_common_root_of_monic_unit_constant
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0)) (x : ℂ)
    (hx : aeval x p = 0) (hdx : aeval x p.derivative = 0)
    (hunique : ∀ y : ℂ, aeval y p = 0 → aeval y p.derivative = 0 → y = x) :
    x = 1 ∨ x = -1 := by
  let pQ := p.map (algebraMap ℤ ℚ)
  have heval (r : ℤ[X]) (y : ℂ) :
      aeval y (r.map (algebraMap ℤ ℚ)) = aeval y r := by
    exact (aeval_eq_aeval_map (by ext a; simp) r y).symm
  have hpQ : pQ ≠ 0 := (hp.map (algebraMap ℤ ℚ)).ne_zero
  have hxQ : aeval x pQ = 0 := by rw [heval]; exact hx
  have hdxQ : aeval x pQ.derivative = 0 := by
    change aeval x (p.map (algebraMap ℤ ℚ)).derivative = 0
    rw [derivative_map, heval]
    exact hdx
  have huniqQ : ∀ y : ℂ, aeval y pQ = 0 → aeval y pQ.derivative = 0 → y = x := by
    intro y hy hyd
    apply hunique y
    · rwa [heval] at hy
    · change aeval y (p.map (algebraMap ℤ ℚ)).derivative = 0 at hyd
      rwa [derivative_map, heval] at hyd
  obtain ⟨q, hq⟩ := unique_common_root_is_rational pQ hpQ x hxQ hdxQ huniqQ
  have hqr : aeval q p = 0 := by
    apply (algebraMap ℚ ℂ).injective
    rw [map_zero]
    change (IsScalarTower.toAlgHom ℤ ℚ ℂ) (aeval q p) = 0
    rw [← aeval_algHom_apply]
    change aeval (q : ℂ) p = 0
    rwa [hq]
  rcases rational_root_of_monic_unit_constant p hp hc hqr with h | h
  · left
    rw [← hq, h]
    norm_num
  · right
    rw [← hq, h]
    norm_num

/-- A unique multiple complex root of a monic integer unit polynomial
must be one of the two rational units. -/
theorem unique_repeated_root_of_monic_unit_constant
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0)) (x : ℂ)
    (hx : 1 < (p.map (algebraMap ℤ ℂ)).rootMultiplicity x)
    (hunique : ∀ y : ℂ, 1 < (p.map (algebraMap ℤ ℂ)).rootMultiplicity y → y = x) :
    x = 1 ∨ x = -1 := by
  let P := p.map (algebraMap ℤ ℂ)
  have hP : P ≠ 0 := (hp.map (algebraMap ℤ ℂ)).ne_zero
  have heval (r : ℤ[X]) (y : ℂ) : (r.map (algebraMap ℤ ℂ)).eval y = aeval y r := by
    rw [eval_map]
    rfl
  have hroots := (one_lt_rootMultiplicity_iff_isRoot hP).mp hx
  apply unique_common_root_of_monic_unit_constant p hp hc x
  · simpa only [P, IsRoot, heval] using hroots.1
  · simpa only [P, derivative_map, IsRoot, heval] using hroots.2
  · intro y hy hyd
    apply hunique y
    apply (one_lt_rootMultiplicity_iff_isRoot hP).mpr
    constructor
    · simpa only [P, IsRoot, heval] using hy
    · simpa only [P, derivative_map, IsRoot, heval] using hyd

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SpectralPerturbation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instContinuousSMulPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsModuleTopologyPadicLocalAlgebra _root_.OAI.PrimeDegreePackets.instIsTopologicalRingLocalAlgebra _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Separated real spectra under small perturbations

The spectral step in EKL (2006), Lemma 5.3, can be obtained from diagonal
row dominance and the intermediate value theorem. The determinant keeps
its sign along a perturbation whose row sums are smaller than the
corresponding diagonal entries. Opposite endpoint signs then locate a
real characteristic root in each separated interval.
-/

noncomputable section
open Set Matrix
open scoped BigOperators Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma det_diagonal_add_ne_zero_of_row_norm
    (d : ι → ℝ) (E : Matrix ι ι ℝ)
    (hE : ∀ i, ∑ j, ‖E i j‖ < ‖d i‖) :
    (diagonal d + E).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hsum : (∑ j ∈ Finset.univ.erase i, ‖E i j‖) + ‖E i i‖ =
      ∑ j, ‖E i j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have htri : ‖d i‖ ≤ ‖d i + E i i‖ + ‖E i i‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (d i + E i i) (E i i)
  have hoff : (∑ j ∈ Finset.univ.erase i, ‖(diagonal d + E) i j‖) =
      ∑ j ∈ Finset.univ.erase i, ‖E i j‖ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Matrix.add_apply, diagonal_apply_ne _ hji.symm]
  rw [hoff, Matrix.add_apply, diagonal_apply_eq]
  have := hE i
  linarith

lemma det_diagonal_add_same_sign
    (d : ι → ℝ) (E : Matrix ι ι ℝ)
    (hE : ∀ i, ∑ j, ‖E i j‖ < ‖d i‖) :
    0 < (diagonal d).det * (diagonal d + E).det := by
  let f : ℝ → ℝ := fun t => (diagonal d + t • E).det
  have hcont : Continuous f := by
    apply Continuous.matrix_det
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht
    apply det_diagonal_add_ne_zero_of_row_norm
    intro i
    calc
      (∑ j, ‖(t • E) i j‖) = t * ∑ j, ‖E i j‖ := by
        simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg ht.1, Finset.mul_sum]
      _ ≤ ∑ j, ‖E i j‖ := mul_le_of_le_one_left (Finset.sum_nonneg fun _ _ => norm_nonneg _) ht.2
      _ < ‖d i‖ := hE i
  have hn0 : f 0 ≠ 0 := hn 0 ⟨le_rfl, zero_le_one⟩
  have hpos : 0 < f 0 * f 1 := by
    apply isPreconnected_Icc.lt_of_ne (hcont.continuousOn.const_mul (f 0))
    · intro t ht
      exact mul_ne_zero hn0 (hn t ht)
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, mul_self_pos.mpr hn0⟩
    · exact ⟨zero_le_one, le_rfl⟩
  simpa only [f, zero_smul, add_zero, one_smul] using hpos

lemma continuous_has_root_of_mul_neg {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hab : a < b) (hsign : f a * f b < 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  have hfa : f a ≠ 0 := by intro h; simp [h] at hsign
  have hfb : f b ≠ 0 := by intro h; simp [h] at hsign
  have hzero : ∃ x ∈ Icc a b, f x = 0 := by
    rcases mul_neg_iff.mp hsign with h | h
    · exact intermediate_value_Icc' hab.le hf ⟨h.2.le, h.1.le⟩
    · exact intermediate_value_Icc hab.le hf ⟨h.1.le, h.2.le⟩
  obtain ⟨x, hx, hfx⟩ := hzero
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, hfx⟩
  · intro hax
    exact hfa (hax ▸ hfx)
  · intro hxb
    exact hfb (hxb ▸ hfx)

/-- A diagonal root bracket survives perturbations controlled by row sums. -/
theorem charpoly_has_root_of_diagonal_bracket
    (w : ι → ℝ) (E : Matrix ι ι ℝ) {a b : ℝ} (hab : a < b)
    (ha : ∀ i, ∑ j, ‖E i j‖ < ‖a - w i‖)
    (hb : ∀ i, ∑ j, ‖E i j‖ < ‖b - w i‖)
    (hsign : (∏ i, (a - w i)) * (∏ i, (b - w i)) < 0) :
    ∃ x ∈ Ioo a b, (diagonal w + E).charpoly.eval x = 0 := by
  have heval (z : ℝ) :
      (diagonal w + E).charpoly.eval z =
        (diagonal (fun i => z - w i) + -E).det := by
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.add_apply]
      ring
    · simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.add_apply, hij]
  have hsa := det_diagonal_add_same_sign (fun i => a - w i) (-E) (by simpa using ha)
  have hsb := det_diagonal_add_same_sign (fun i => b - w i) (-E) (by simpa using hb)
  rw [Matrix.det_diagonal, ← heval] at hsa hsb
  apply continuous_has_root_of_mul_neg (Polynomial.continuous _).continuousOn hab
  rcases mul_neg_iff.mp hsign with h | h
  · have hleft : 0 < (diagonal w + E).charpoly.eval a := ((mul_pos_iff.mp hsa).resolve_right (fun hn => (not_lt_of_gt h.1) hn.1)).2
    have hright : (diagonal w + E).charpoly.eval b < 0 := ((mul_pos_iff.mp hsb).resolve_left (fun hp => (not_lt_of_gt hp.1) h.2)).2
    exact mul_neg_of_pos_of_neg hleft hright
  · have hleft : (diagonal w + E).charpoly.eval a < 0 := ((mul_pos_iff.mp hsa).resolve_left (fun hp => (not_lt_of_gt hp.1) h.1)).2
    have hright : 0 < (diagonal w + E).charpoly.eval b := ((mul_pos_iff.mp hsb).resolve_right (fun hn => (not_lt_of_gt h.2) hn.1)).2
    exact mul_neg_of_neg_of_pos hleft hright

lemma diagonal_bracket_sign (w : ι → ℝ) (k : ι) {a b : ℝ}
    (ha : a < w k) (hb : w k < b)
    (hout : ∀ j, j ≠ k → w j < a ∨ b < w j) :
    (∏ i, (a - w i)) * (∏ i, (b - w i)) < 0 := by
  rw [← Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  apply mul_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr ha) (sub_pos.mpr hb)
  · apply Finset.prod_pos
    intro j hj
    rcases hout j (Finset.mem_erase.mp hj).1 with h | h
    · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (h.trans (ha.trans hb)))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr ((ha.trans hb).trans h)) (sub_neg.mpr h)

/-- Disjoint brackets around all diagonal entries supply every characteristic root.
The bounds are on the actual perturbation, not on an assumed spectrum. -/
theorem charpoly_roots_of_separated_brackets
    (w : ι → ℝ) (E : Matrix ι ι ℝ) (a b : ι → ℝ)
    (ha : ∀ i, a i < w i) (hb : ∀ i, w i < b i)
    (hout : ∀ i j, j ≠ i → w j < a i ∨ b i < w j)
    (hdis : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i)
    (hEa : ∀ i k, ∑ j, ‖E k j‖ < ‖a i - w k‖)
    (hEb : ∀ i k, ∑ j, ‖E k j‖ < ‖b i - w k‖) :
    ∃ r : ι → ℝ, (∀ i, r i ∈ Ioo (a i) (b i) ∧
      (diagonal w + E).charpoly.eval (r i) = 0) ∧
      Function.Injective r ∧
      (diagonal w + E).charpoly.roots = (Finset.univ.image r).val ∧
      (diagonal w + E).charpoly.Splits ∧
      (diagonal w + E).charpoly.Separable := by
  have hex (i : ι) : ∃ x ∈ Ioo (a i) (b i), (diagonal w + E).charpoly.eval x = 0 :=
    charpoly_has_root_of_diagonal_bracket w E ((ha i).trans (hb i)) (hEa i) (hEb i)
      (diagonal_bracket_sign w i (ha i) (hb i) (hout i))
  choose r hr hroot using hex
  have hinj : Function.Injective r := by
    intro i j heq
    by_contra hne
    rcases hdis i j hne with h | h
    · have hi := (hr i).2
      have hj := (hr j).1
      linarith
    · have hi := (hr i).1
      have hj := (hr j).2
      linarith
  have hroots : (diagonal w + E).charpoly.roots = (Finset.univ.image r).val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hroot i
    · rw [Matrix.charpoly_natDegree_eq_dim, Finset.card_image_of_injective _ hinj,
        Finset.card_univ]
    · exact (Matrix.charpoly_monic _).ne_zero
  have hsplit : (diagonal w + E).charpoly.Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    rw [hroots]
    change (Finset.univ.image r).card = (diagonal w + E).charpoly.natDegree
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Matrix.charpoly_natDegree_eq_dim]
  refine ⟨r, fun i => ⟨hr i, hroot i⟩, hinj, hroots, hsplit, ?_⟩
  apply (Polynomial.nodup_roots_iff_of_splits (Matrix.charpoly_monic _).ne_zero hsplit).mp
  rw [hroots]
  exact (Finset.univ.image r).nodup

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_SpectralSeparation
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The spectral estimate for exceptional returns

EKL (2006), Lemma 5.3, in the form needed for real diagonal return
matrices. A fixed neighborhood of the identity works for every set of
logarithmic diagonal weights separated by more than one.
-/

noncomputable section
open Set Matrix
open scoped BigOperators Classical

namespace DukePrimeDegree

lemma spectralRelativeRadius_pos : 0 < spectralRelativeRadius := by
  unfold spectralRelativeRadius
  have : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

lemma exp_gap_distance {x y : ℝ} (hxy : (1 / 2 : ℝ) ≤ |x - y|) :
    spectralRelativeRadius * Real.exp y ≤ ‖Real.exp x - Real.exp y‖ := by
  have he : 2 ≤ Real.exp (1 / 2 : ℝ) + Real.exp (-(1 / 2 : ℝ)) := by
    linarith [Real.add_one_le_exp (1 / 2 : ℝ), Real.add_one_le_exp (-(1 / 2 : ℝ))]
  have hy : 0 < Real.exp y := Real.exp_pos y
  rcases le_total x y with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hxy
    have hx : x ≤ y - 1 / 2 := by linarith
    have hexp := Real.exp_le_exp.mpr hx
    rw [Real.exp_sub] at hexp
    have hr : Real.exp y / Real.exp (1 / 2 : ℝ) =
        Real.exp y * Real.exp (-(1 / 2 : ℝ)) := by rw [Real.exp_neg, div_eq_mul_inv]
    rw [hr] at hexp
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hle))]
    unfold spectralRelativeRadius
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hxy
    have hx : y + 1 / 2 ≤ x := by linarith
    have hexp := Real.exp_le_exp.mpr hx
    rw [Real.exp_add] at hexp
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hle))]
    unfold spectralRelativeRadius
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hy.le]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma logarithmic_gap_brackets (ell : ι → ℝ)
    (hgap : ∀ i j, i ≠ j → 1 < |ell i - ell j|) :
    (∀ i j, j ≠ i → Real.exp (ell j) < Real.exp (ell i - 1 / 2) ∨
      Real.exp (ell i + 1 / 2) < Real.exp (ell j)) ∧
    (∀ i j, i ≠ j → Real.exp (ell i + 1 / 2) ≤ Real.exp (ell j - 1 / 2) ∨
      Real.exp (ell j + 1 / 2) ≤ Real.exp (ell i - 1 / 2)) ∧
    (∀ i k, spectralRelativeRadius * Real.exp (ell k) ≤
      ‖Real.exp (ell i - 1 / 2) - Real.exp (ell k)‖) ∧
    (∀ i k, spectralRelativeRadius * Real.exp (ell k) ≤
      ‖Real.exp (ell i + 1 / 2) - Real.exp (ell k)‖) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hji
    rcases lt_abs.mp (hgap i j hji.symm) with h | h
    · left
      apply Real.exp_lt_exp.mpr
      linarith
    · right
      apply Real.exp_lt_exp.mpr
      linarith
  · intro i j hij
    rcases lt_abs.mp (hgap i j hij) with h | h
    · right
      apply Real.exp_le_exp.mpr
      linarith
    · left
      apply Real.exp_le_exp.mpr
      linarith
  · intro i k
    apply exp_gap_distance
    by_cases hik : i = k
    · subst k
      norm_num
    · rcases lt_abs.mp (hgap i k hik) with h | h
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith)]
        linarith
  · intro i k
    apply exp_gap_distance
    by_cases hik : i = k
    · subst k
      norm_num
    · rcases lt_abs.mp (hgap i k hik) with h | h
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith)]
        linarith

/-- The roots of a small perturbation of a logarithmically separated positive
 diagonal matrix are real, distinct, and stay in their half-unit log brackets. -/
theorem real_spectrum_of_logarithmic_gaps (ell : ι → ℝ)
    (hgap : ∀ i j, i ≠ j → 1 < |ell i - ell j|)
    (H : Matrix ι ι ℝ)
    (hH : ∀ i, ∑ j, ‖(H - 1) i j‖ < spectralRelativeRadius) :
    ∃ r : ι → ℝ, Function.Injective r ∧
      (∀ i, 0 < r i ∧ |Real.log (r i) - ell i| < 1 / 2 ∧
        (H * diagonal (fun j => Real.exp (ell j))).charpoly.eval (r i) = 0) ∧
      (H * diagonal (fun j => Real.exp (ell j))).charpoly.roots =
        (Finset.univ.image r).val ∧
      (H * diagonal (fun j => Real.exp (ell j))).charpoly.Splits ∧
      (H * diagonal (fun j => Real.exp (ell j))).charpoly.Separable := by
  let D := diagonal (fun i => Real.exp (ell i))
  let E := D * (H - 1)
  have hrow (i : ι) : ∑ j, ‖E i j‖ < spectralRelativeRadius * Real.exp (ell i) := by
    have hs : (∑ j, ‖E i j‖) = Real.exp (ell i) * ∑ j, ‖(H - 1) i j‖ := by
      simp only [E, D, Matrix.diagonal_mul, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Finset.mul_sum]
    rw [hs, mul_comm spectralRelativeRadius]
    exact mul_lt_mul_of_pos_left (hH i) (Real.exp_pos _)
  obtain ⟨hout, hdis, ha, hb⟩ := logarithmic_gap_brackets ell hgap
  obtain ⟨r, hr, hinj, hroots, hsplit, hsep⟩ := charpoly_roots_of_separated_brackets
    (fun i => Real.exp (ell i)) E
    (fun i => Real.exp (ell i - 1 / 2)) (fun i => Real.exp (ell i + 1 / 2))
    (fun i => Real.exp_lt_exp.mpr (by linarith))
    (fun i => Real.exp_lt_exp.mpr (by linarith)) hout hdis
    (fun i k => (hrow k).trans_le (ha i k))
    (fun i k => (hrow k).trans_le (hb i k))
  have hmatrix : diagonal (fun i => Real.exp (ell i)) + E = D * H := by
    dsimp [E]
    rw [mul_sub, Matrix.mul_one, add_sub_cancel]
  have hpoly : (diagonal (fun i => Real.exp (ell i)) + E).charpoly = (H * D).charpoly := by
    rw [hmatrix, Matrix.charpoly_mul_comm]
  rw [hpoly] at hr hroots hsplit hsep
  refine ⟨r, hinj, ?_, hroots, hsplit, hsep⟩
  intro i
  have hpos : 0 < r i := (Real.exp_pos _).trans (hr i).1.1
  refine ⟨hpos, ?_, (hr i).2⟩
  rw [abs_lt]
  have hlo : ell i - 1 / 2 < Real.log (r i) := by
    exact (Real.lt_log_iff_exp_lt hpos).mpr (hr i).1.1
  have hhi : Real.log (r i) < ell i + 1 / 2 := by
    exact (Real.log_lt_iff_lt_exp hpos).mpr (hr i).1.2
  constructor <;> linarith

/-- The row bound defines a fixed neighborhood of the identity. -/
lemma eventually_spectral_row_bound :
    ∀ᶠ H : Matrix ι ι ℝ in nhds 1,
      ∀ i, ∑ j, ‖(H - 1) i j‖ < spectralRelativeRadius := by
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (fun H : Matrix ι ι ℝ => ∑ j, ‖(H - 1) i j‖) := by
    apply continuous_finsetSum
    intro j _
    fun_prop
  have hsmall : (∑ j, ‖((1 : Matrix ι ι ℝ) - 1) i j‖) < spectralRelativeRadius := by
    simpa using spectralRelativeRadius_pos
  exact hc.continuousAt.eventually (gt_mem_nhds hsmall)

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ExceptionalPolynomial
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A scalar double block in an integral return matrix

The centralizer of the root SL₂ has a scalar two-dimensional block.
The remaining block in a sufficiently separated return has simple real
spectrum. Such a return matrix cannot be conjugate to an integral
special-linear matrix unless the scalar eigenvalue is ±1.
-/

noncomputable section
open Polynomial Matrix
open scoped Classical

namespace DukePrimeDegree

lemma double_factor_unique_repeated_root
    {K : Type*} [Field K] (q : K[X]) (hq : q ≠ 0) (hsep : q.Separable) (c : K) :
    1 < ((X - C c) ^ 2 * q).rootMultiplicity c ∧
      ∀ y : K, 1 < ((X - C c) ^ 2 * q).rootMultiplicity y → y = c := by
  constructor
  · rw [mul_comm, rootMultiplicity_mul_X_sub_C_pow hq]
    omega
  · intro y hy
    by_contra hne
    have hn : (X - C c) ^ 2 * q ≠ 0 := mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero c)) hq
    rw [rootMultiplicity_mul hn] at hy
    have hnot : ¬ ((X - C c) ^ 2 : K[X]).IsRoot y := by
      simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_C, pow_eq_zero_iff (by norm_num : 2 ≠ 0),
        sub_eq_zero]
      exact hne
    rw [rootMultiplicity_eq_zero hnot, zero_add] at hy
    exact (not_lt_of_ge (rootMultiplicity_le_one_of_separable hsep y)) hy

/-- The arithmetic obstruction only needs a scalar double factor and a
separable residual polynomial, not a complete eigenbasis. -/
theorem integer_unit_polynomial_double_factor
    (p : ℤ[X]) (hp : p.Monic) (hc : IsUnit (p.coeff 0))
    (c : ℝ) (q : ℝ[X]) (hq : q.Monic) (hsep : q.Separable)
    (hfactor : p.map (algebraMap ℤ ℝ) = (X - C c) ^ 2 * q) :
    c = 1 ∨ c = -1 := by
  have hfactorC : p.map (algebraMap ℤ ℂ) =
      (X - C (c : ℂ)) ^ 2 * q.map (algebraMap ℝ ℂ) := by
    have h := congrArg (fun r : ℝ[X] => r.map (algebraMap ℝ ℂ)) hfactor
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℝ ℂ,
      Complex.coe_algebraMap] using h
  have hqC : q.map (algebraMap ℝ ℂ) ≠ 0 := (hq.map _).ne_zero
  have hsepC : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  obtain ⟨hcroot, hunique⟩ := double_factor_unique_repeated_root
    (q.map (algebraMap ℝ ℂ)) hqC hsepC (c : ℂ)
  rw [← hfactorC] at hcroot hunique
  rcases unique_repeated_root_of_monic_unit_constant p hp hc (c : ℂ) hcroot hunique with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h

/-- No integral special-linear return can have a nonunit scalar double
block and a separable complementary characteristic factor. -/
theorem integer_sl_double_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Matrix.SpecialLinearGroup ι ℤ)
    (c : ℝ) (q : ℝ[X]) (hq : q.Monic) (hsep : q.Separable)
    (hfactor : g.val.charpoly.map (algebraMap ℤ ℝ) = (X - C c) ^ 2 * q) :
    c = 1 ∨ c = -1 := by
  apply integer_unit_polynomial_double_factor g.val.charpoly g.val.charpoly_monic _ c q hq hsep hfactor
  apply isUnit_of_dvd_one
  refine ⟨(-1 : ℤ) ^ Fintype.card ι, ?_⟩
  have h := g.val.det_eq_sign_charpoly_coeff
  rw [g.property] at h
  simpa only [mul_comm] using h

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitRecurrence
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recurrence with close orbit parameters

For the exceptional-return argument, recurrence is needed in the parameter
topology of an orbit, which need not be closed in the ambient quotient.
A countable cover by compact parameter neighborhoods makes their images
measurable, and ordinary Poincaré recurrence supplies the required return.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [SecondCountableTopology G]
variable [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology G] in
lemma exists_compact_close_parameter_neighborhood (U : Set G) (hU : U ∈ 𝓝 1) (g : G) :
    ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 g ∧ ∀ a ∈ K, ∀ b ∈ K, a⁻¹ * b ∈ U := by
  have hc : Continuous (fun p : G × G => p.1⁻¹ * p.2) := continuous_fst.inv.mul continuous_snd
  have ht : Tendsto (fun p : G × G => p.1⁻¹ * p.2) (𝓝 (g, g)) (𝓝 1) := by
    simpa only [inv_mul_cancel] using hc.tendsto (g, g)
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp (ht.eventually hU)
  obtain ⟨K, hKg, hKsub, hKc⟩ := local_compact_nhds (inter_mem hV hW)
  refine ⟨K, hKc, hKg, ?_⟩
  intro a ha b hb
  exact hVW (show (a, b) ∈ V ×ˢ W from ⟨(hKsub ha).1, (hKsub hb).2⟩)

/-- Poincaré recurrence in the topology of orbit parameters. This does not
require the orbit image to be closed or its inverse parametrization continuous. -/
theorem exists_close_parameters_of_orbit_recurrence
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (f : X → X) (hf : MeasurePreserving f μ μ)
    (ψ : G → X) (hψ : Continuous ψ) (hfull : ∀ᵐ x ∂μ, x ∈ range ψ)
    (U : Set G) (hU : U ∈ 𝓝 1) (N : ℕ) :
    ∃ n > N, ∃ a b : G, a⁻¹ * b ∈ U ∧ f^[n] (ψ a) = ψ b := by
  choose K hKc hKg hKsmall using exists_compact_close_parameter_neighborhood U hU
  obtain ⟨t, ht, hcover⟩ := countable_cover_nhds hKg
  have hpos : ∃ g ∈ t, μ (ψ '' K g) ≠ 0 := by
    by_contra hnone
    have hz : ∀ g ∈ t, μ (ψ '' K g) = 0 := by simpa only [not_exists, not_and, not_not] using hnone
    have hnot : ∀ᵐ x ∂μ, ∀ g ∈ t, x ∉ ψ '' K g := by
      apply (ae_ball_iff ht).mpr
      intro g hg
      exact measure_eq_zero_iff_ae_notMem.mp (hz g hg)
    obtain ⟨x, hx, hn⟩ := (hfull.and hnot).exists
    obtain ⟨a, rfl⟩ := hx
    have ha : a ∈ ⋃ g ∈ t, K g := by rw [hcover]; trivial
    obtain ⟨g, hg, haK⟩ := mem_iUnion₂.mp ha
    exact hn g hg ⟨a, haK, rfl⟩
  obtain ⟨g, _, hg⟩ := hpos
  have hmeas : MeasurableSet (ψ '' K g) := ((hKc g).image hψ).isClosed.measurableSet
  obtain ⟨n, hn, hret⟩ := hf.conservative.exists_gt_measure_inter_ne_zero hmeas.nullMeasurableSet hg N
  obtain ⟨x, hx, hfx⟩ := nonempty_of_measure_ne_zero hret
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hbeq⟩ := hfx
  exact ⟨n, hn, a, b, hKsmall g a ha b hb, hbeq.symm⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_QuotientReturn
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral matrices from recurrence on a subgroup orbit

A late return with close subgroup parameters in the arithmetic quotient
produces a conjugate integral special-linear matrix. This is the orbit
recurrence step in EKL Theorem 5.1.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree

open PrimeDegreePackets

/-- Recurrence on a closed subgroup orbit produces integral conjugates
of late flow elements multiplied by arbitrarily small subgroup elements. -/
theorem exists_integral_return_of_closed_orbit {n : ℕ}
    (H : Subgroup (G n)) (hH : IsClosed (H : Set (G n)))
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n) (hfull : ∀ᵐ y ∂μ, ∃ h : H, rightAction x (h : G n) = y)
    (a : G n) (hinv : μ.map (fun y => rightAction y a) = μ)
    (U : Set H) (hU : U ∈ 𝓝 1) (N : ℕ) :
    ∃ m > N, ∃ h : H, h ∈ U ∧ ∃ q : G n,
      ∃ γ : Matrix.SpecialLinearGroup (Fin n) ℤ,
        q⁻¹ * (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) * q =
          a ^ m * (h : G n) := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let T : X n → X n := fun y => rightAction y a
  have hT : MeasurePreserving T μ μ := ⟨(continuous_rightAction a).measurable, hinv⟩
  have hψ : Continuous (fun h : H => rightAction x (h : G n)) :=
    (continuous_rightAction_uncurry n).comp (continuous_const.prodMk continuous_subtype_val)
  have hV : Inv.inv ⁻¹' U ∈ 𝓝 (1 : H) := by
    have ht : Tendsto (Inv.inv : H → H) (𝓝 1) (𝓝 1) := by
      simpa only [inv_one] using continuous_inv.tendsto (1 : H)
    exact ht.eventually hU
  obtain ⟨m, hm, r, s, hclose, hret⟩ :=
    exists_close_parameters_of_orbit_recurrence μ T hT
      (fun h : H => rightAction x (h : G n)) hψ hfull _ hV N
  have hiter (k : ℕ) (y : X n) : T^[k] y = rightAction y (a ^ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      change rightAction (rightAction y (a ^ k)) a = rightAction y (a ^ (k + 1))
      rw [rightAction_mul, pow_succ]
  rw [hiter, rightAction_mul] at hret
  obtain ⟨q₀, hq₀⟩ := Quotient.exists_rep x
  rw [← hq₀] at hret
  have heq : Quotient.mk (QuotientGroup.rightRel (integralGroup n))
      (q₀ * ((r : G n) * a ^ m)) =
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (q₀ * (s : G n)) := hret
  have hΓ : (q₀ * ((r : G n) * a ^ m)) * (q₀ * (s : G n))⁻¹ ∈ integralGroup n :=
    (QuotientGroup.rightRel_apply).mp (Quotient.exact heq.symm)
  obtain ⟨γ, hγ⟩ := hΓ
  refine ⟨m, hm, s⁻¹ * r, ?_, q₀ * (r : G n), γ, ?_⟩
  · simpa only [mem_preimage, mul_inv_rev, inv_inv] using hclose
  · rw [hγ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The root-pair centralizer

The common centralizer of opposite elementary root groups has a scalar
block on their two coordinates. This gives the concrete matrix form
needed to apply the integral scalar-block obstruction to orbit returns.
-/

noncomputable section
open Set Matrix
open scoped Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma rootPairCentralizer_isClosed {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    IsClosed (rootPairCentralizer hij : Set (G n)) :=
  Set.isClosed_centralizer _

lemma rootPairCentralizer_entries {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : g ∈ rootPairCentralizer hij) :
    g.val i i = g.val j j ∧ g.val i j = 0 ∧ g.val j i = 0 ∧
      ∀ r : Fin n, r ≠ i → r ≠ j →
        g.val r i = 0 ∧ g.val r j = 0 ∧ g.val i r = 0 ∧ g.val j r = 0 := by
  obtain ⟨h₁, h₂⟩ := (mem_rootPairCentralizer hij g).mp hg
  obtain ⟨hc₁, hr₁, hd⟩ := (commutes_root_one_iff hij g).mp h₁
  obtain ⟨hc₂, hr₂, _⟩ := (commutes_root_one_iff hij.symm g).mp h₂
  exact ⟨hd, hc₂ i hij, hc₁ j hij.symm,
    fun r hri hrj => ⟨hc₁ r hri, hc₂ r hrj, hr₂ r hri, hr₁ r hrj⟩⟩

/-- Reindexing the common centralizer of opposite roots separates its
scalar two-dimensional block from the complementary matrix. -/
theorem rootPairCentralizer_block {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (g : G n) (hg : g ∈ rootPairCentralizer hij) :
    ∃ c : ℝ, ∃ B : Matrix (Fin m) (Fin m) ℝ,
      Matrix.reindex e e g.val =
        Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B := by
  let i := e.symm (Sum.inl 0)
  let j := e.symm (Sum.inl 1)
  let c := g.val i i
  let B : Matrix (Fin m) (Fin m) ℝ := fun r s => g.val (e.symm (Sum.inr r)) (e.symm (Sum.inr s))
  obtain ⟨hd, h01, h10, ho⟩ := rootPairCentralizer_entries hij g hg
  have hn (r : Fin m) : e.symm (Sum.inr r) ≠ i ∧ e.symm (Sum.inr r) ≠ j := by
    constructor
    all_goals intro heq; apply_fun e at heq; simp [i, j] at heq
  refine ⟨c, B, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · fin_cases r <;> fin_cases s
    · rfl
    · simpa [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.diagonal, i, j] using h01
    · simpa [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.diagonal, i, j] using h10
    · simpa [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.diagonal, c, i, j] using hd.symm
  · fin_cases r
    · exact (ho _ (hn s).1 (hn s).2).2.2.1
    · exact (ho _ (hn s).1 (hn s).2).2.2.2
  · fin_cases s
    · exact (ho _ (hn r).1 (hn r).2).1
    · exact (ho _ (hn r).1 (hn r).2).2.1
  · rfl

/-- The scalar-block obstruction after the coordinate reindexing used for
an arbitrary opposite-root pair in the arithmetic quotient. -/
theorem reindexed_integral_scalar_block {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (q : G n) (γ : Matrix.SpecialLinearGroup (Fin n) ℤ)
    (c : ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (hsep : B.charpoly.Separable)
    (hblock : Matrix.reindex e e
      (q⁻¹ * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * q).val =
        Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B) :
    c = 1 ∨ c = -1 := by
  have hcancel : q.val * (q⁻¹).val = 1 := by
    change (q * q⁻¹).val = 1
    simp
  have hconj :
      (q⁻¹ * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * q).val.charpoly =
        γ.val.charpoly.map (algebraMap ℤ ℝ) := by
    change ((q⁻¹).val * γ.val.map (Int.castRingHom ℝ) * q.val).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, hcancel, one_mul, Matrix.charpoly_map]
    rfl
  have hpoly : γ.val.charpoly.map (algebraMap ℤ ℝ) =
      (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 2 => c)) 0 0 B).charpoly := by
    rw [← hconj, ← Matrix.charpoly_reindex e]
    exact congrArg Matrix.charpoly hblock
  apply integer_sl_double_factor γ c B.charpoly B.charpoly_monic hsep
  rw [hpoly, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_diagonal]
  simp [pow_two]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralizerFlow
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small centralizer factors in late diagonal returns

The root-pair centralizer supplies a scalar double block and a complementary
matrix. A fixed neighborhood controls that complementary matrix; late
neutral diagonal times separate its spectrum and keep the scalar away
from the rational units.
-/

noncomputable section
open Set Filter Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootPairCentralizer_block_explicit {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (g : G n) (hg : g ∈ rootPairCentralizer hij) :
    Matrix.reindex e e g.val = Matrix.fromBlocks
      (Matrix.diagonal (fun _ : Fin 2 => g.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))))
      0 0 (complementaryMatrix e g) := by
  obtain ⟨c, B, h⟩ := rootPairCentralizer_block e hij g hg
  have hc := congrArg (fun M => M (Sum.inl 0) (Sum.inl 0)) h
  change g.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) = c at hc
  have hB : complementaryMatrix e g = B := by
    ext r s
    exact congrArg (fun M => M (Sum.inr r) (Sum.inr s)) h
  rwa [← hc, ← hB] at h

lemma complementaryMatrix_diagonal_mul {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (t : ℝ) (g : G n) :
    complementaryMatrix e (diagonalOneParameter ell hell t * g) =
      Matrix.diagonal (fun r => Real.exp (ell (e.symm (Sum.inr r)) * t)) *
        complementaryMatrix e g := by
  ext r s
  change (Matrix.diagonal (fun i => Real.exp (ell i * t)) * g.val)
    (e.symm (Sum.inr r)) (e.symm (Sum.inr s)) = _
  simp only [Matrix.diagonal_mul, complementaryMatrix]

lemma complementaryMatrix_one {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    complementaryMatrix e 1 = 1 := by
  ext r s
  simp [complementaryMatrix, Matrix.one_apply, e.symm.injective.eq_iff]

lemma eventually_separated_scaled_weights {m : ℕ} (w : Fin m → ℝ)
    (hw : Function.Injective w) :
    ∀ᶠ k : ℕ in atTop, ∀ r s : Fin m, r ≠ s →
      1 < |w r * (k : ℝ) - w s * (k : ℝ)| := by
  apply Filter.eventually_all.mpr
  intro r
  apply Filter.eventually_all.mpr
  intro s
  by_cases hrs : r = s
  · exact Filter.Eventually.of_forall fun _ h => (h hrs).elim
  · have hp : 0 < |w r - w s| := abs_pos.mpr (sub_ne_zero.mpr (hw.ne hrs))
    have ht : Tendsto (fun k : ℕ => |w r - w s| * (k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hp
    filter_upwards [ht.eventually (eventually_gt_atTop (1 : ℝ))] with k hk _
    have habs : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
    simpa only [← sub_mul, abs_mul, habs] using hk

lemma eventually_scalar_between_zero_one {a : ℝ} (ha : a < 0) :
    ∀ᶠ k : ℕ in atTop, ∀ c : ℝ, 0 < c → c < Real.exp 1 →
      0 < Real.exp (a * (k : ℝ)) * c ∧ Real.exp (a * (k : ℝ)) * c < 1 := by
  have ht : Tendsto (fun k : ℕ => a * (k : ℝ)) atTop atBot :=
    tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg ha
  filter_upwards [ht.eventually (eventually_lt_atBot (-1 : ℝ))] with k hk c hc hc'
  refine ⟨mul_pos (Real.exp_pos _) hc, ?_⟩
  calc
    Real.exp (a * (k : ℝ)) * c < Real.exp (a * (k : ℝ)) * Real.exp 1 :=
      mul_lt_mul_of_pos_left hc' (Real.exp_pos _)
    _ = Real.exp (a * (k : ℝ) + 1) := (Real.exp_add _ _).symm
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

/-- A fixed identity neighborhood simultaneously controls the scalar and
complementary blocks of every centralizer factor. -/
lemma eventually_small_centralizer_blocks {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1)) :
    ∀ᶠ g : rootPairCentralizer hij in 𝓝 1,
      0 < g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) ∧
      g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) < Real.exp 1 ∧
      ∀ r, ∑ s, ‖(complementaryMatrix e g.val - 1) r s‖ < spectralRelativeRadius := by
  have hc : Continuous (fun g : rootPairCentralizer hij =>
      g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))) := by fun_prop
  have hscalar : Tendsto (fun g : rootPairCentralizer hij =>
      g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))) (𝓝 1) (𝓝 1) := by
    convert hc.tendsto (1 : rootPairCentralizer hij) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  have hpos := hscalar.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hupper := hscalar.eventually (gt_mem_nhds
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)))
  have hcB : Continuous (fun g : rootPairCentralizer hij => complementaryMatrix e g.val) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro s
    change Continuous (fun g : rootPairCentralizer hij =>
      g.val.val (e.symm (Sum.inr r)) (e.symm (Sum.inr s)))
    fun_prop
  have ht : Tendsto (fun g : rootPairCentralizer hij => complementaryMatrix e g.val)
      (𝓝 1) (𝓝 1) := by
    have h := hcB.tendsto (1 : rootPairCentralizer hij)
    change Tendsto _ _ (𝓝 (complementaryMatrix e (1 : G n))) at h
    rwa [complementaryMatrix_one] at h
  exact hpos.and (hupper.and (ht.eventually eventually_spectral_row_bound))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralizerContraction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded diagonal returns in a root centralizer

A matrix centralizing one root can have entries outside the opposite-root
centralizer only in expanding directions of a suitable diagonal flow.
Bounded conjugates along arbitrarily late times therefore centralize both
roots. This is the matrix step in EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma eq_zero_of_bounded_exp_mul
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop)
    {c : ℝ} (hc : 0 < c) (a B : ℝ)
    (hb : ∀ᶠ k in atTop, |Real.exp (c * t k) * a| ≤ B) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.mpr ha
  have he := Real.tendsto_exp_atTop.comp (ht.const_mul_atTop hc)
  have hexp : Tendsto (fun k => |Real.exp (c * t k) * a|) atTop atTop := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _), Function.comp_apply] using he.atTop_mul_const ha'
  exact (not_isBoundedUnder_of_tendsto_atTop hexp) ⟨B, eventually_map.mpr hb⟩

/-- Each strictly expanding matrix entry must vanish if the conjugates
remain bounded along a sequence of times tending to infinity. -/
lemma conjugation_expanding_entry_eq_zero {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (g : G n)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) (B : ℝ)
    (hb : ∀ᶠ k in atTop, ∀ r s,
      |(diagonalOneParameter ell hell (t k) * g *
        diagonalOneParameter ell hell (-t k)).val r s| ≤ B)
    {r s : Fin n} (hrs : ell s < ell r) : g.val r s = 0 := by
  apply eq_zero_of_bounded_exp_mul ht (sub_pos.mpr hrs) _ B
  filter_upwards [hb] with k hk
  simpa only [conjugation_entry] using hk r s

/-- With the two distinguished weights extremal, bounded conjugates in
one root centralizer belong to the common centralizer of opposite roots. -/
theorem rootPairCentralizer_of_bounded_conjugates {n : ℕ}
    {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (hijw : ell j < ell i)
    (hmiddle : ∀ r, r ≠ i → r ≠ j → ell j < ell r ∧ ell r < ell i)
    (g : G n)
    (hg : g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) (B : ℝ)
    (hb : ∀ᶠ k in atTop, ∀ r s,
      |(diagonalOneParameter ell hell (t k) * g *
        diagonalOneParameter ell hell (-t k)).val r s| ≤ B) :
    g ∈ rootPairCentralizer hij := by
  apply (mem_rootPairCentralizer hij g).mpr
  refine ⟨hg, (commutes_root_one_iff hij.symm g).mpr ?_⟩
  have hz {r s : Fin n} (h : ell s < ell r) : g.val r s = 0 :=
    conjugation_expanding_entry_eq_zero ell hell g ht B hb h
  obtain ⟨_, _, hd⟩ := (commutes_root_one_iff hij g).mp hg
  refine ⟨?_, ?_, hd.symm⟩
  · intro r hrj
    by_cases hri : r = i
    · subst r
      exact hz hijw
    · exact hz (hmiddle r hri hrj).1
  · intro s hsi
    by_cases hsj : s = j
    · subst s
      exact hz hijw
    · exact hz (hmiddle s hsi hsj).2

/-- Poincaré recurrence supplies the unbounded sequence needed by the
matrix criterion, even when conjugate bounds hold only on returns to a
measurable set. -/
theorem ae_rootPairCentralizer_of_recurrent_conjugates
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (E : Set Y) (hE : MeasurableSet E)
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (hijw : ell j < ell i)
    (hmiddle : ∀ r, r ≠ i → r ≠ j → ell j < ell r ∧ ell r < ell i)
    (g : Y → G n)
    (hg : ∀ x ∈ E, g x * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g x)
    (B : ℝ)
    (hb : ∀ x ∈ E, ∀ k : ℕ, T^[k] x ∈ E → ∀ r s,
      |(diagonalOneParameter ell hell (k : ℝ) * g x *
        diagonalOneParameter ell hell (-(k : ℝ))).val r s| ≤ B) :
    ∀ᵐ x ∂μ, x ∈ E → g x ∈ rootPairCentralizer hij := by
  filter_upwards [hT.conservative.ae_mem_imp_frequently_image_mem hE.nullMeasurableSet]
    with x hx
  intro hxE
  obtain ⟨ns, hns, hret⟩ := extraction_of_frequently_atTop (hx hxE)
  apply rootPairCentralizer_of_bounded_conjugates hij ell hell hijw hmiddle
    (g x) (hg x hxE) (t := fun k => (ns k : ℝ))
    (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop) B
  exact Filter.Eventually.of_forall (fun k => hb x hxE (ns k) (hret k))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SmallCentralizer
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compact balls in a root centralizer

The diagonal with weights 1, -1, and 0 contracts the centralizer of the
corresponding root in reverse time. In particular, it preserves each
closed matrix ball in that centralizer. These compact sets give measurable
sets of small returns in the proof of EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Elementwise

namespace DukePrimeDegree
open PrimeDegreePackets

lemma isCompact_matrixClosedBall (n : ℕ) (r : ℝ) : IsCompact (matrixClosedBall n r) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage (isCompact_closedBall _ _)

lemma mem_matrixClosedBall_iff {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (g : G n) :
    g ∈ matrixClosedBall n r ↔ ∀ a b, |g.val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b| ≤ r := by
  change dist g.val 1 ≤ r ↔ _
  rw [dist_eq_norm, Matrix.norm_le_iff hr]
  simp only [Matrix.sub_apply, Real.norm_eq_abs]

lemma matrixClosedBall_subset_matrixBall {n : ℕ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) : matrixClosedBall n r ⊆ matrixBall n R := by
  intro g hg a b
  exact lt_of_le_of_lt ((mem_matrixClosedBall_iff hr g).mp hg a b) hrR

lemma entry_bound_of_mem_matrixClosedBall {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r) {g : G n} (hg : g ∈ matrixClosedBall n r) (a b : Fin n) :
    |g.val a b| ≤ r + 1 := by
  have h := (mem_matrixClosedBall_iff hr g).mp hg a b
  by_cases hab : a = b
  · subst b
    rw [Matrix.one_apply_eq] at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Matrix.one_apply_ne hab, sub_zero] at h
    linarith

lemma rootContractionWeights_gap {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootContractionWeights i j j < rootContractionWeights i j i := by
  simp [rootContractionWeights, hij, Ne.symm hij]

lemma rootContractionWeights_middle {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {r : Fin n} (hri : r ≠ i) (hrj : r ≠ j) :
    rootContractionWeights i j j < rootContractionWeights i j r ∧
      rootContractionWeights i j r < rootContractionWeights i j i := by
  simp [rootContractionWeights, hij, Ne.symm hij, hri, hrj]

lemma rootContractionWeights_entry_nonneg {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n)
    (hg : g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g)
    {r s : Fin n} (hentry : g.val r s ≠ 0) :
    0 ≤ rootContractionWeights i j r - rootContractionWeights i j s := by
  obtain ⟨hcol, hrow, _⟩ := (commutes_root_one_iff hij g).mp hg
  by_cases hrj : r = j
  · subst r
    have hsj : s = j := by
      by_contra h
      exact hentry (hrow s h)
    subst s
    simp
  by_cases hsi : s = i
  · subst s
    have hri : r = i := by
      by_contra h
      exact hentry (hcol r h)
    subst r
    simp
  by_cases hri : r = i <;> by_cases hsj : s = j
  all_goals norm_num [rootContractionWeights, hrj, hsi, hri, hsj, hij, Ne.symm hij]

/-- Reverse diagonal time preserves the closed ball in the single-root
centralizer, because every allowed off-diagonal entry contracts. -/
theorem rootCentralizer_conjugate_mem_closedBall {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {r : ℝ} (hr : 0 ≤ r) (g : G n) (hgball : g ∈ matrixClosedBall n r)
    (hg : g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g) (t : ℝ) (ht : 0 ≤ t) :
    diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) (-t) * g *
      diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t ∈
        matrixClosedBall n r := by
  rw [mem_matrixClosedBall_iff hr] at hgball ⊢
  intro a b
  have he := conjugation_entry (rootContractionWeights i j)
    (rootContractionWeights_sum i j) g (-t) a b
  rw [neg_neg] at he
  rw [he]
  by_cases hab : a = b
  · subst b
    simpa only [sub_self, zero_mul, Real.exp_zero, one_mul] using hgball a a
  rw [Matrix.one_apply_ne hab, sub_zero]
  by_cases hg0 : g.val a b = 0
  · simp [hg0, hr]
  have hw := rootContractionWeights_entry_nonneg hij g hg hg0
  have hc : Real.exp ((rootContractionWeights i j a - rootContractionWeights i j b) * -t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hw (neg_nonpos.mpr ht))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 1 * |g.val a b| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ r := by simpa only [one_mul, Matrix.one_apply_ne hab, sub_zero] using hgball a b

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SmallReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small quotient returns centralize both roots

For a fixed neutral return parameter, compact sets of possible small
return matrices give measurable sets of returning points. Conjugation in
the contracting direction preserves the single-root centralizer ball;
uniqueness of quotient lifts then identifies returning matrices exactly.
Poincaré recurrence proves the fixed-parameter form of EKL Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma isClosed_compactReturnSet {n : ℕ} (K : Set (G n)) (hK : IsCompact K) (b : G n) :
    IsClosed (compactReturnSet K b) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (X n × K) := {p | rightAction p.1 p.2.val = rightAction p.1 b}
  have hS : IsClosed S := isClosed_eq
    ((continuous_rightAction_uncurry n).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    ((continuous_rightAction b).comp continuous_fst)
  have hproj := isClosedMap_fst_of_compactSpace S hS
  convert hproj using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [compactReturnSet, mem_ofPred_eq, mem_image, S, Prod.exists, Subtype.exists]
  aesop

/-- A fixed neutral return parameter has, almost everywhere, no small
single-root-centralizing lift outside the opposite-root centralizer. -/
theorem ae_small_rootCentralizer_return_in_pair
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (b : G (d + 1))
    (hcomm : ∀ t : ℝ,
      b * diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t =
        diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t * b)
    (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (U : Set (X (d + 1))) (hU : MeasurableSet U)
    (hinj : ∀ x ∈ U, Set.InjOn (fun g => rightAction x g) (matrixBall (d + 1) R))
    (K : Set (G (d + 1))) (hK : IsCompact K)
    (hKsmall : ∀ g ∈ K, g ∈ matrixClosedBall (d + 1) r ∧
      g * Matrix.SpecialLinearGroup.transvection hij 1 =
        Matrix.SpecialLinearGroup.transvection hij 1 * g) :
    ∀ᵐ x ∂μ, x ∈ U → ∀ g ∈ K, rightAction x g = rightAction x b →
      g ∈ rootPairCentralizer hij := by
  let D := diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j)
  let T : X (d + 1) → X (d + 1) := fun x => rightAction x (D (-1))
  let E := U ∩ compactReturnSet K b
  have hE : MeasurableSet E := hU.inter (isClosed_compactReturnSet K hK b).measurableSet
  let g : X (d + 1) → G (d + 1) := fun x =>
    if hx : x ∈ E then Classical.choose hx.2 else 1
  have hg (x : X (d + 1)) (hx : x ∈ E) :
      g x ∈ K ∧ rightAction x (g x) = rightAction x b := by
    dsimp only [g]
    rw [dite_eq_left hx]
    exact Classical.choose_spec hx.2
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable, ?_⟩
    dsimp only [T, D]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hiter (k : ℕ) (x : X (d + 1)) : T^[k] x = rightAction x (D (-(k : ℝ))) := by
    induction k with
    | zero => simp [D, diagonalOneParameter_zero]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      dsimp only [T, D]
      rw [rightAction_mul, ← diagonalOneParameter_add]
      congr 2
      push_cast
      ring
  have hbound (x : X (d + 1)) (hx : x ∈ E) (k : ℕ) (hk : T^[k] x ∈ E) :
      ∀ a c, |(D (k : ℝ) * g x * D (-(k : ℝ))).val a c| ≤ r + 1 := by
    let y := T^[k] x
    have hy : y = rightAction x (D (-(k : ℝ))) := hiter k x
    have hgy := hg y hk
    have hbackball : D (-(k : ℝ)) * g y * D (k : ℝ) ∈ matrixClosedBall (d + 1) r :=
      rootCentralizer_conjugate_mem_closedBall hij hr (g y)
        (hKsmall _ hgy.1).1 (hKsmall _ hgy.1).2 (k : ℝ) (Nat.cast_nonneg k)
    have hbackret : rightAction x (D (-(k : ℝ)) * g y * D (k : ℝ)) = rightAction x b := by
      calc
        _ = rightAction (rightAction y (g y)) (D (k : ℝ)) := by
          rw [hy]
          simp only [rightAction_mul, mul_assoc]
        _ = rightAction (rightAction y b) (D (k : ℝ)) := congrArg _ hgy.2
        _ = rightAction x b := by
          rw [hy, rightAction_mul, rightAction_mul, hcomm]
          dsimp only [D]
          rw [← mul_assoc, diagonalOneParameter_neg]
          simp
    have heq : D (-(k : ℝ)) * g y * D (k : ℝ) = g x :=
      hinj x hx.1 (matrixClosedBall_subset_matrixBall hr hrR hbackball)
        (matrixClosedBall_subset_matrixBall hr hrR (hKsmall _ (hg x hx).1).1)
        (hbackret.trans (hg x hx).2.symm)
    have hconj : D (k : ℝ) * g x * D (-(k : ℝ)) = g y := by
      rw [← heq]
      dsimp only [D]
      rw [diagonalOneParameter_neg]
      group
    intro a c
    rw [hconj]
    exact entry_bound_of_mem_matrixClosedBall hr (hKsmall _ hgy.1).1 a c
  have hpair := ae_rootPairCentralizer_of_recurrent_conjugates μ T hT E hE hij
    (rootContractionWeights i j) (rootContractionWeights_sum i j)
    (rootContractionWeights_gap hij) (fun a hai haj => rootContractionWeights_middle hij hai haj)
    g (fun x hx => (hKsmall _ (hg x hx).1).2) (r + 1) hbound
  filter_upwards [hpair] with x hx
  intro hxU z hz hret
  have hxE : x ∈ E := ⟨hxU, z, hz, hret⟩
  have heq : z = g x := hinj x hxU
    (matrixClosedBall_subset_matrixBall hr hrR (hKsmall _ hz).1)
    (matrixClosedBall_subset_matrixBall hr hrR (hKsmall _ (hg x hxE).1).1)
    (hret.trans (hg x hxE).2.symm)
  exact heq ▸ hx hxE

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_StrongReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous strong returns

The fixed-parameter small-return theorem extends to a whole subgroup by
separability and closedness. This removes the parameter-dependent null
sets in the exceptional-return argument of EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma mem_singleRootCentralizer {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    g ∈ singleRootCentralizer hij ↔ g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g := by
  simp only [singleRootCentralizer, Subgroup.mem_centralizer_iff, mem_singleton_iff,
    forall_eq, eq_comm]

lemma matrixBall_subset_matrixClosedBall {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    matrixBall n r ⊆ matrixClosedBall n r := by
  intro g hg
  exact (mem_matrixClosedBall_iff hr g).mpr fun a b => (hg a b).le

/-- On a fixed injectivity chart, one conull set works for every parameter
in any subgroup commuting with the contracting diagonal and the root. -/
theorem ae_strong_returns_on_chart
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (H : Subgroup (G (d + 1)))
    (hHroot : ∀ b : H, (b : G (d + 1)) ∈ singleRootCentralizer hij)
    (hHdiag : ∀ b : H, ∀ t : ℝ,
      (b : G (d + 1)) * diagonalOneParameter (rootContractionWeights i j)
        (rootContractionWeights_sum i j) t =
      diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t * b)
    (r R : ℝ) (hr : 0 ≤ r) (hrR : r < R)
    (U : Set (X (d + 1))) (hU : MeasurableSet U)
    (hinj : ∀ x ∈ U, Set.InjOn (fun g => rightAction x g) (matrixBall (d + 1) R)) :
    ∀ᵐ x ∂μ, x ∈ U → ∀ b : H, ∀ g ∈ matrixBall (d + 1) r,
      g ∈ singleRootCentralizer hij → rightAction x g = rightAction x b →
        g ∈ rootPairCentralizer hij := by
  let : SecondCountableTopology H := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense H
  let K : Set (G (d + 1)) := matrixClosedBall (d + 1) r ∩ singleRootCentralizer hij
  have hK : IsCompact K := (isCompact_matrixClosedBall (d + 1) r).inter_right
    (Set.isClosed_centralizer _)
  have hfixed : ∀ b : H, ∀ᵐ x ∂μ, x ∈ U → ∀ g ∈ K,
      rightAction x g = rightAction x b → g ∈ rootPairCentralizer hij := by
    intro b
    apply ae_small_rootCentralizer_return_in_pair d hij μ hA b (hHdiag b) r R hr hrR U hU hinj K hK
    intro g hg
    exact ⟨hg.1, (mem_singleRootCentralizer hij g).mp hg.2⟩
  have hall : ∀ᵐ x ∂μ, ∀ b ∈ S, x ∈ U → ∀ g ∈ K,
      rightAction x g = rightAction x b → g ∈ rootPairCentralizer hij :=
    (ae_ball_iff hSc).mpr fun b _ => hfixed b
  filter_upwards [hall] with x hx
  intro hxU b g hgball hgroot hret
  let f : H → G (d + 1) := fun c => g * (b : G (d + 1))⁻¹ * c
  have hf : Continuous f := (continuous_const.mul continuous_const).mul continuous_subtype_val
  have hfb : f b = g := by dsimp [f]; group
  let W : Set H := f ⁻¹' matrixBall (d + 1) r
  have hW : IsOpen W := (matrixBall_isOpen _ _).preimage hf
  have hbW : b ∈ W := by change f b ∈ matrixBall (d + 1) r; rwa [hfb]
  have hbcl : b ∈ closure (S ∩ W) := by
    apply mem_closure_iff.mpr
    intro V hV hbV
    obtain ⟨c, hcS, hcV, hcW⟩ := hSd.exists_mem_open (hV.inter hW) ⟨b, hbV, hbW⟩
    exact ⟨c, hcV, hcS, hcW⟩
  have hsub : S ∩ W ⊆ f ⁻¹' (rootPairCentralizer hij : Set (G (d + 1))) := by
    rintro c ⟨hcS, hcW⟩
    apply hx c hcS hxU (f c)
    · refine ⟨matrixBall_subset_matrixClosedBall hr hcW, ?_⟩
      exact (singleRootCentralizer hij).mul_mem
        ((singleRootCentralizer hij).mul_mem hgroot
          ((singleRootCentralizer hij).inv_mem (hHroot b))) (hHroot c)
    · dsimp only [f]
      rw [← rightAction_mul, ← rightAction_mul, hret, rightAction_mul, rightAction_mul]
      congr 1
      group
  have hclosed : IsClosed (f ⁻¹' (rootPairCentralizer hij : Set (G (d + 1)))) :=
    (rootPairCentralizer_isClosed hij).preimage hf
  have hmem := hclosed.closure_subset_iff.mpr hsub hbcl
  change f b ∈ rootPairCentralizer hij at hmem
  rwa [hfb] at hmem

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ExceptionalReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exceptional-return strengthening

Outside one null set, every sufficiently small lift of a return along the
root-pair centralizer, if it centralizes the chosen root, centralizes both
roots. In particular this applies to every neutral diagonal return. This
is the implication from exceptional to strong exceptional returns in
EKL (2006), Lemma 4.2, on the actual arithmetic quotient.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootContractionWeights_swap {n : ℕ} (i j r : Fin n) :
    rootContractionWeights j i r = -rootContractionWeights i j r := by
  unfold rootContractionWeights
  ring

lemma rootPairCentralizer_commutes_contraction {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (g : G n) (hg : g ∈ rootPairCentralizer hij) (t : ℝ) :
    g * diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t =
      diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t * g := by
  obtain ⟨hijg, hjig⟩ := (mem_rootPairCentralizer hij g).mp hg
  have hw {r s : Fin n} (hentry : g.val r s ≠ 0) :
      rootContractionWeights i j r = rootContractionWeights i j s := by
    have h₁ := rootContractionWeights_entry_nonneg hij g hijg hentry
    have h₂ := rootContractionWeights_entry_nonneg hij.symm g hjig hentry
    rw [rootContractionWeights_swap i j r, rootContractionWeights_swap i j s] at h₂
    linarith
  ext r s
  change (g.val * Matrix.diagonal (fun a => Real.exp (rootContractionWeights i j a * t))) r s =
    (Matrix.diagonal (fun a => Real.exp (rootContractionWeights i j a * t)) * g.val) r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hzero : g.val r s = 0
  · simp [hzero]
  · rw [hw hzero]
    ring

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ergodic orbits accumulate on the support of a restricted measure

For a countable ergodic group action, almost every orbit meets every
positive-measure set. Applying this to a countable topological basis
shows that the orbit's visits to a measurable set accumulate on the
support of the restricted measure. This is the orbit-density step of
EKL (2006), Proposition 4.3.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree

variable {H Y : Type*} [Group H] [Countable H] [MulAction H Y]
  [MeasurableSpace Y] [MeasurableConstSMul H Y]

/-- The saturation of a positive-measure set is conull in an ergodic action. -/
theorem ae_orbit_meets_of_measure_ne_zero
    (μ : Measure Y) [ErgodicSMul H Y μ]
    (S : Set Y) (hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    ∀ᵐ y ∂μ, ∃ h : H, h • y ∈ S := by
  let V : Set Y := ⋃ h : H, (fun y => h • y) ⁻¹' S
  have hV : MeasurableSet V := MeasurableSet.iUnion fun h => hS.preimage (measurable_const_smul h)
  have hinv (g : H) : (fun y => g • y) ⁻¹' V = V := by
    ext y
    simp only [V, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨h * g, by simpa only [mul_smul] using hh⟩
    · rintro ⟨h, hh⟩
      refine ⟨h * g⁻¹, ?_⟩
      simpa only [mul_smul, inv_smul_smul] using hh
  have hconst := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (μ := μ) hV
    (fun g => by rw [hinv g]; exact Filter.EventuallyEq.rfl)
  rcases eventuallyConst_set.mp hconst with hfull | hnull
  · simpa only [V, mem_iUnion, mem_preimage] using hfull
  · have hz : μ V = 0 := measure_eq_zero_iff_ae_notMem.mpr hnull
    apply (hpos (measure_mono_null (s := S) (t := V) ?_ hz)).elim
    intro y hy
    exact mem_iUnion.mpr ⟨1, by simpa using hy⟩

variable [TopologicalSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]

/-- Almost every orbit's visits to `K` accumulate on the entire support
of the restricted measure; no closedness assumption on `K` is needed. -/
theorem ae_restricted_support_subset_orbit_closure
    (μ : Measure Y) [ErgodicSMul H Y μ] (K : Set Y) (hK : MeasurableSet K) :
    ∀ᵐ y ∂μ, (μ.restrict K).support ⊆
      closure {z : Y | z ∈ K ∧ ∃ h : H, h • y = z} := by
  have hall : ∀ᵐ y ∂μ, ∀ U ∈ TopologicalSpace.countableBasis Y,
      μ (K ∩ U) ≠ 0 → ∃ h : H, h • y ∈ K ∩ U := by
    apply (ae_ball_iff (TopologicalSpace.countable_countableBasis Y)).mpr
    intro U hU
    by_cases hp : μ (K ∩ U) = 0
    · exact ae_of_all _ (fun _ h => (h hp).elim)
    · have hUm := (TopologicalSpace.isOpen_of_mem_countableBasis hU).measurableSet
      exact (ae_orbit_meets_of_measure_ne_zero (H := H) μ _ (hK.inter hUm) hp).mono
        fun y hy _ => hy
  filter_upwards [hall] with y hy
  intro z hz
  apply mem_closure_iff.mpr
  intro V hV hzV
  obtain ⟨U, hU, hzU, hUV⟩ :=
    (TopologicalSpace.isBasis_countableBasis Y).exists_subset_of_mem_open hzV hV
  have hUp : 0 < μ (K ∩ U) := by
    have hp := (Measure.mem_support_iff_forall z).mp hz U
      ((TopologicalSpace.isOpen_of_mem_countableBasis hU).mem_nhds hzU)
    rwa [Measure.restrict_apply (TopologicalSpace.isOpen_of_mem_countableBasis hU).measurableSet,
      inter_comm] at hp
  obtain ⟨h, hhK, hhU⟩ := hy U hU hUp.ne'
  exact ⟨h • y, hUV hhU, hhK, h, rfl⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_OrbitConcentration
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concentration from compactly controlled returns

If nearby returns of an ergodic action lie in a fixed compact set of
translations in a larger group, the whole measure lies on one orbit of
that group. This is the topological-measure argument in the reverse
implication of EKL (2006), Proposition 4.3.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree

variable {H C Y : Type*} [Group H] [Countable H] [Group C]
  [TopologicalSpace C] [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [MulAction H Y] [MeasurableConstSMul H Y] [MulAction C Y] [ContinuousSMul C Y]

/-- Strong returns with compact translation parameters force a single
orbit, once the ergodic component has a support point in the return set. -/
theorem ae_on_single_orbit_of_compact_returns
    (μ : Measure Y) [ErgodicSMul H Y μ]
    (φ : H →* C) (hφ : ∀ h : H, ∀ y : Y, (φ h) • y = h • y)
    (K : Set Y) (hK : MeasurableSet K)
    (z : Y) (hz : z ∈ (μ.restrict K).support)
    (V : Set Y) (hV : IsOpen V) (hzV : z ∈ V)
    (L : Set C) (hL : IsCompact L)
    (hret : ∀ u ∈ K ∩ V, ∀ h : H, h • u ∈ K ∩ V →
      ∃ c ∈ L, c • u = h • u) :
    ∀ᵐ y ∂μ, ∃ c : C, c • z = y := by
  filter_upwards [ae_restricted_support_subset_orbit_closure (H := H) μ K hK] with y hy
  let F : Set Y := {w | w ∈ K ∧ ∃ h : H, h • y = w}
  have hzF : z ∈ closure F := hy hz
  obtain ⟨u, huV, huK, h, hhu⟩ := mem_closure_iff.mp hzF V hV hzV
  have hu : u ∈ K ∩ V := ⟨huK, huV⟩
  let P : Set Y := (fun c : C => c • u) '' L
  have hP : IsClosed P := (hL.image (continuous_id.smul continuous_const)).isClosed
  have hsub : V ∩ F ⊆ P := by
    rintro w ⟨hwV, hwK, k, hkw⟩
    have hkhu : (k * h⁻¹) • u = w := by
      rw [← hhu, mul_smul, inv_smul_smul]
      exact hkw
    obtain ⟨c, hc, hcu⟩ := hret u hu (k * h⁻¹) (by rw [hkhu]; exact ⟨hwK, hwV⟩)
    exact ⟨c, hc, hcu.trans hkhu⟩
  have hzVF : z ∈ closure (V ∩ F) := by
    apply mem_closure_iff.mpr
    intro W hW hzW
    obtain ⟨w, hwWV, hwF⟩ := mem_closure_iff.mp hzF (W ∩ V) (hW.inter hV) ⟨hzW, hzV⟩
    exact ⟨w, hwWV.1, hwWV.2, hwF⟩
  have hzP : z ∈ P := hP.closure_subset_iff.mpr hsub hzVF
  obtain ⟨c, _, hcu⟩ := hzP
  have heq : (c * φ h) • y = z := by
    rw [mul_smul, hφ, hhu]
    exact hcu
  refine ⟨(c * φ h)⁻¹, ?_⟩
  rw [← heq, inv_smul_smul]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_QuotientNeighborhoods
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small relative lifts on the arithmetic quotient

Open quotient charts provide a neighborhood in which any two points are
related by a matrix in a prescribed identity neighborhood. This is the
local lifting step used with compactly controlled centralizer returns.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rightOrbitMap_isOpen {n : ℕ} (x : X n) :
    IsOpenMap (fun g : G n => rightAction x g) := by
  induction x using Quotient.inductionOn with
  | h q =>
    intro U hU
    change IsOpen ((fun g => Quotient.mk _ (q * g)) '' U)
    rw [← Set.image_image]
    exact (quotient_covering n).isOpenMap _ ((Homeomorph.mulLeft q).isOpenMap _ hU)

/-- Any identity neighborhood gives a quotient neighborhood with small
relative lifts between all of its points. -/
theorem exists_open_small_relative_lifts {n : ℕ}
    (x : X n) (W : Set (G n)) (hW : W ∈ 𝓝 1) :
    ∃ V : Set (X n), IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V, ∃ g ∈ W, rightAction y g = z := by
  obtain ⟨K, _, hK, hKsmall⟩ := exists_compact_close_parameter_neighborhood W hW (1 : G n)
  let V := (fun g => rightAction x g) '' interior K
  refine ⟨V, rightOrbitMap_isOpen x _ isOpen_interior, ?_, ?_⟩
  · exact ⟨1, mem_interior_iff_mem_nhds.mpr hK, by simp⟩
  · rintro y ⟨a, ha, rfl⟩ z ⟨b, hb, rfl⟩
    refine ⟨a⁻¹ * b, hKsmall a (interior_subset ha) b (interior_subset hb), ?_⟩
    rw [rightAction_mul]
    congr 1
    group

/-- The matrix-ball form needed for exceptional returns. -/
theorem exists_open_matrix_relative_lifts {n : ℕ} (x : X n) {r : ℝ} (hr : 0 < r) :
    ∃ V : Set (X n), IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ z ∈ V, ∃ g ∈ matrixBall n r, rightAction y g = z :=
  exists_open_small_relative_lifts x _ ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))

lemma rightSubgroupAction_continuous {n : ℕ} (C : Subgroup (G n)) :
    let := rightSubgroupAction C
    ContinuousSMul (MulOpposite C) (X n) := by
  let := rightSubgroupAction C
  constructor
  exact (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk ((continuous_subtype_val.comp MulOpposite.continuous_unop).comp continuous_fst))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootOrbitConcentration
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Root-pair orbit concentration from strong returns

This is the arithmetic-quotient specialization of the compact-return
argument in EKL (2006), Proposition 4.3. The countable ergodic action may
be a dense subgroup of the neutral diagonal group. A positive-measure
set with strong returns forces the component onto one root-pair orbit.
-/

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootPair_orbit_of_strong_returns
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (H : Type*) [Group H] [Countable H]
    (φ : H →* MulOpposite (rootPairCentralizer hij))
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hE : let := rightSubgroupAction (rootPairCentralizer hij)
      let := MulAction.compHom (X (d + 1)) φ
      ErgodicSMul H (X (d + 1)) μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hstrong : ∀ x ∈ K, ∀ h : H, rightAction x ((φ h).unop : G (d + 1)) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x ((φ h).unop : G (d + 1)) →
          g ∈ rootPairCentralizer hij) :
    ∃ z : X (d + 1), ∀ᵐ y ∂μ,
      ∃ c : rootPairCentralizer hij, rightAction z (c : G (d + 1)) = y := by
  let := rightSubgroupAction (rootPairCentralizer hij)
  let := rightSubgroupAction_continuous (rootPairCentralizer hij)
  let := MulAction.compHom (X (d + 1)) φ
  let : MeasurableConstSMul H (X (d + 1)) :=
    ⟨fun h => (continuous_rightAction ((φ h).unop : G (d + 1))).measurable⟩
  let : ErgodicSMul H (X (d + 1)) μ := hE
  have hμK : μ.restrict K ≠ 0 := by
    intro hz
    have he := congrArg (fun ν : Measure (X (d + 1)) => ν univ) hz
    exact hpos (by simpa using he)
  obtain ⟨z, hz⟩ := Measure.nonempty_support hμK
  obtain ⟨V, hV, hzV, hrel⟩ := exists_open_matrix_relative_lifts z hr
  let L : Set (MulOpposite (rootPairCentralizer hij)) :=
    {c | (c.unop : G (d + 1)) ∈ matrixClosedBall (d + 1) r}
  have hL : IsCompact L := by
    have he : Topology.IsClosedEmbedding
        (fun c : MulOpposite (rootPairCentralizer hij) => (c.unop : G (d + 1))) :=
      (rootPairCentralizer_isClosed hij).isClosedEmbedding_subtypeVal.comp
        MulOpposite.opHomeomorph.symm.isClosedEmbedding
    exact he.isCompact_preimage (isCompact_matrixClosedBall (d + 1) r)
  have hret : ∀ u ∈ K ∩ V, ∀ h : H, h • u ∈ K ∩ V →
      ∃ c ∈ L, c • u = h • u := by
    intro u hu h hh
    obtain ⟨g, hg, hgu⟩ := hrel u hu.2 (h • u) hh.2
    have hgC : g ∈ rootPairCentralizer hij := hstrong u hu.1 h hh.1 g hg hgu
    refine ⟨MulOpposite.op ⟨g, hgC⟩, ?_, ?_⟩
    · exact matrixBall_subset_matrixClosedBall hr.le hg
    · exact hgu
  have hconc := ae_on_single_orbit_of_compact_returns μ φ (fun _ _ => rfl)
    K hK z hz V hV hzV L hL hret
  refine ⟨z, ?_⟩
  filter_upwards [hconc] with y hy
  obtain ⟨c, hc⟩ := hy
  exact ⟨c.unop, hc⟩

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralDiagonal
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The neutral diagonal group

The kernel of one root character, inside trace-zero real weights, is the
group used for the ergodic decomposition in EKL's low-entropy argument.
Its diagonal representation takes values in the opposite-root centralizer.
-/

noncomputable section
open Set Matrix
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_neutralDiagonalHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (neutralDiagonalHom hij) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  change Continuous (fun u : Multiplicative (neutralWeightSubgroup i j) =>
    Matrix.diagonal (fun r => Real.exp (u.toAdd.val r * 1)) a b)
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, mul_one]
    exact Real.continuous_exp.comp ((continuous_apply a).comp
      (continuous_subtype_val.comp (show Continuous (fun u : Multiplicative
        (neutralWeightSubgroup i j) => u.toAdd) from continuous_id)))
  · simp only [Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_NeutralAction
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The neutral diagonal action on the lattice quotient

The concrete neutral weight subgroup acts continuously by right diagonal
translations. Its measure-preserving action follows from full diagonal
invariance, and every trace-zero neutral weight is represented in it.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma neutralDiagonalAction_continuous {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    let := neutralDiagonalAction hij
    ContinuousSMul (Multiplicative (neutralWeightSubgroup i j)) (X n) := by
  let := neutralDiagonalAction hij
  constructor
  exact (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk
      ((continuous_subtype_val.comp (continuous_neutralDiagonalHom hij)).comp continuous_fst))

lemma neutralDiagonal_preserving
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1)))
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (u : Multiplicative (neutralWeightSubgroup i j)) :
    let := neutralDiagonalAction hij
    MeasurePreserving (fun x : X (d + 1) => u • x) μ μ := by
  let := neutralDiagonalAction hij
  refine ⟨(continuous_rightAction _).measurable, ?_⟩
  change μ.map (fun x => rightAction x (diagonalOneParameter u.toAdd.val u.toAdd.property.1 1)) = μ
  rw [diagonalOneParameter_eq_diagonalFlow]
  exact hA _

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_NoCentralizerOrbit
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Excluding a probability measure on a root centralizer orbit

This is the consequence of EKL Theorem 5.1 and Proposition 5.2 needed in
the low-entropy argument. The neutral direction is explicit: its double
weight is negative and its complementary weights are distinct.
-/

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem no_invariant_rootPair_orbit_of_weights {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (hneut : ell (e.symm (Sum.inl 0)) = ell (e.symm (Sum.inl 1)))
    (hneg : ell (e.symm (Sum.inl 0)) < 0)
    (hdist : Function.Injective (fun r : Fin m => ell (e.symm (Sum.inr r))))
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n)
    (hfull : ∀ᵐ y ∂μ, ∃ h : rootPairCentralizer hij, rightAction x (h : G n) = y)
    (hinv : μ.map (fun y => rightAction y (diagonalOneParameter ell hell 1)) = μ) :
    False := by
  let U : Set (rootPairCentralizer hij) := {g |
    0 < g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) ∧
    g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) < Real.exp 1 ∧
    ∀ r, ∑ s, ‖(complementaryMatrix e g.val - 1) r s‖ < spectralRelativeRadius}
  have hU : U ∈ 𝓝 1 := eventually_small_centralizer_blocks e hij
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((eventually_separated_scaled_weights _ hdist).and (eventually_scalar_between_zero_one hneg))
  obtain ⟨k, hk, h, hh, q, γ, hγ⟩ := exists_integral_return_of_closed_orbit
    (rootPairCentralizer hij) (rootPairCentralizer_isClosed hij)
    μ x hfull (diagonalOneParameter ell hell 1) hinv U hU N
  obtain ⟨hgap, hscalar⟩ := hN k hk.le
  obtain ⟨hc0, hc1, hBsmall⟩ := hh
  let R : G n := diagonalOneParameter ell hell (k : ℝ) * h.val
  have hR : R ∈ rootPairCentralizer hij :=
    (rootPairCentralizer hij).mul_mem
      (diagonal_mem_rootPairCentralizer hij ell hell hneut _) h.property
  have hγR : q⁻¹ * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * q = R := by
    simpa only [R, ← diagonalOneParameter_nat] using hγ
  have hBsep : (complementaryMatrix e R).charpoly.Separable := by
    obtain ⟨_, _, _, _, _, hs⟩ := real_spectrum_of_logarithmic_gaps
      (fun r => ell (e.symm (Sum.inr r)) * (k : ℝ)) hgap
      (complementaryMatrix e h.val) hBsmall
    dsimp [R]
    rw [complementaryMatrix_diagonal_mul, Matrix.charpoly_mul_comm]
    exact hs
  let c := R.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))
  have hc : c = Real.exp (ell (e.symm (Sum.inl 0)) * (k : ℝ)) *
      h.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) := by
    change (Matrix.diagonal (fun i => Real.exp (ell i * (k : ℝ))) * h.val.val)
      (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) = _
    rw [Matrix.diagonal_mul]
  have hcbounds : 0 < c ∧ c < 1 := by
    rw [hc]
    exact hscalar _ hc0 hc1
  have hunit : c = 1 ∨ c = -1 := by
    apply reindexed_integral_scalar_block e q γ c (complementaryMatrix e R) hBsep
    rw [hγR]
    exact rootPairCentralizer_block_explicit e hij R hR
  rcases hunit with hunit | hunit
  · linarith [hcbounds.2]
  · linarith [hcbounds.1]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_CentralizerWeights
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An explicit neutral direction excluding centralizer orbits

The two root coordinates receive the same negative weight. The remaining
coordinates receive distinct positive weights. Their sum is balanced by
the repeated negative weight. This discharges the elementary weight
conditions in the centralizer-orbit exclusion.
-/

noncomputable section
open Set MeasureTheory Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma centralizerWitnessWeights_sum {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    ∑ i, centralizerWitnessWeights e i = 0 := by
  unfold centralizerWitnessWeights
  rw [e.sum_comp, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma centralizerWitnessWeights_neutral {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    centralizerWitnessWeights e (e.symm (Sum.inl 0)) =
      centralizerWitnessWeights e (e.symm (Sum.inl 1)) := by
  simp [centralizerWitnessWeights]

lemma centralizerWitnessWeights_negative {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hm : 0 < m) : centralizerWitnessWeights e (e.symm (Sum.inl 0)) < 0 := by
  have hs : 0 < ∑ r : Fin m, ((r : ℝ) + 1) := by
    apply Finset.sum_pos'
    · intro r _
      positivity
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _, by norm_num⟩
  simp only [centralizerWitnessWeights, Equiv.apply_symm_apply, Sum.elim_inl]
  linarith

lemma centralizerWitnessWeights_injective {n m : ℕ} (e : Fin n ≃ Fin 2 ⊕ Fin m) :
    Function.Injective (fun r : Fin m => centralizerWitnessWeights e (e.symm (Sum.inr r))) := by
  intro r s h
  simp only [centralizerWitnessWeights, Equiv.apply_symm_apply, Sum.elim_inr] at h
  have hval : (r : ℝ) = (s : ℝ) := add_right_cancel h
  apply Fin.ext
  exact_mod_cast hval

/-- No nonzero finite measure invariant under the neutral diagonal group
can be supported on a single root-pair centralizer orbit. -/
theorem no_invariant_rootPair_orbit {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m) (hm : 0 < m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n)
    (hfull : ∀ᵐ y ∂μ, ∃ h : rootPairCentralizer hij, rightAction x (h : G n) = y)
    (hinv : ∀ (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0),
      ell (e.symm (Sum.inl 0)) = ell (e.symm (Sum.inl 1)) →
      μ.map (fun y => rightAction y (diagonalOneParameter ell hell 1)) = μ) : False := by
  exact no_invariant_rootPair_orbit_of_weights e hij (centralizerWitnessWeights e)
    (centralizerWitnessWeights_sum e) (centralizerWitnessWeights_neutral e)
    (centralizerWitnessWeights_negative e hm) (centralizerWitnessWeights_injective e)
    μ x hfull (hinv _ _ (centralizerWitnessWeights_neutral e))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Geometry_RootPairCoordinates
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates for an arbitrary opposite-root pair

Any two distinct coordinates can be placed first, with a nonempty
complement when the degree is at least three. This removes the coordinate
choice from the centralizer-orbit exclusion.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma exists_rootPair_coordinates {n : ℕ} (hn : 2 < n)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ m : ℕ, 0 < m ∧ ∃ e : Fin n ≃ Fin 2 ⊕ Fin m,
      e.symm (Sum.inl 0) = i ∧ e.symm (Sum.inl 1) = j := by
  let f : Fin 2 → Fin n := ![i, j]
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [f, hij, hij.symm] at *
  let C := (Set.range f)ᶜ
  let e₀ : Fin 2 ⊕ C ≃ Fin n :=
    (Equiv.sumCongr (Equiv.ofInjective f hf) (Equiv.refl C)).trans
      (Equiv.Set.sumCompl (Set.range f))
  let e : Fin n ≃ Fin 2 ⊕ Fin (Fintype.card C) :=
    e₀.symm.trans (Equiv.sumCongr (Equiv.refl (Fin 2)) (Fintype.equivFin C))
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  have hk : k ∈ C := by
    rintro ⟨a, ha⟩
    fin_cases a
    · exact hki (by simpa [f] using ha.symm)
    · exact hkj (by simpa [f] using ha.symm)
  have hm : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨⟨k, hk⟩⟩
  refine ⟨Fintype.card C, hm, e, ?_, ?_⟩
  · change f 0 = i
    rfl
  · change f 1 = j
    rfl

/-- The centralizer-orbit exclusion for any pair of distinct coordinates,
with no coordinate or weight choices remaining in the assumptions. -/
theorem no_neutral_invariant_rootPair_orbit {n : ℕ} (hn : 2 < n)
    {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n)
    (hfull : ∀ᵐ y ∂μ, ∃ h : rootPairCentralizer hij, rightAction x (h : G n) = y)
    (hinv : ∀ (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0), ell i = ell j →
      μ.map (fun y => rightAction y (diagonalOneParameter ell hell 1)) = μ) : False := by
  obtain ⟨m, hm, e, hi, hj⟩ := exists_rootPair_coordinates hn i j hij
  subst i
  subst j
  exact no_invariant_rootPair_orbit e hm hij μ x hfull hinv

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_StrongReturnExclusion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Excluding positive-measure sets of strong neutral returns

Ergodic decomposition, the compact-return orbit-concentration argument,
and the arithmetic centralizer-orbit obstruction together exclude a
measurable positive-measure set with uniform strong neutral returns.
This is the consequence of EKL (2006), Proposition 4.3 and Theorem 5.1,
needed for the low-entropy alternative on the arithmetic quotient.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem strong_neutral_return_set_null
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 < r)
    (hstrong : ∀ x ∈ K,
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
      rightAction x (diagonalOneParameter ell hell 1) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
          g ∈ rootPairCentralizer hij) : μ K = 0 := by
  let N := Multiplicative (neutralWeightSubgroup i j)
  let := neutralDiagonalAction hij
  let := neutralDiagonalAction_continuous hij
  let : SecondCountableTopology (neutralWeightSubgroup i j) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology N :=
    (inferInstance : SecondCountableTopology (neutralWeightSubgroup i j))
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense N
  let : Countable s := hs.to_subtype
  let H := FreeGroup s
  let φ : H →* N := FreeGroup.lift (fun a : s => (a : N))
  have hdφ : DenseRange φ := hdense.mono (by
    intro g hg
    exact ⟨FreeGroup.of ⟨g, hg⟩, FreeGroup.lift_apply_of⟩)
  let := MulAction.compHom (X (d + 1)) φ
  let : MeasurableConstSMul H (X (d + 1)) :=
    ⟨fun h => (continuous_const_smul (φ h)).measurable⟩
  have hp (h : H) : MeasurePreserving (fun y : X (d + 1) => h • y) μ μ :=
    neutralDiagonal_preserving d hij μ hA (φ h)
  have hdec := action_ergodic_decomposition μ hp
  let κ := condExpKernel μ (actionInvariantSigma H (X (d + 1)))
  let τ := μ.trim (actionInvariantSigma_le H (X (d + 1)))
  have hzero : ∀ᵐ x ∂τ, κ x K = 0 := by
    filter_upwards [hdec.2] with x hx
    let ν := κ x
    let : ErgodicSMul H (X (d + 1)) ν := hx
    by_contra hpos
    have hν (u : N) : MeasurePreserving (fun y : X (d + 1) => u • y) ν ν :=
      preserving_of_dense_action φ hdφ ν (fun h => measurePreserving_smul h ν) u
    let ψ : H →* MulOpposite (rootPairCentralizer hij) :=
      (neutralDiagonalOppositeHom hij).comp φ
    have hErg : let := rightSubgroupAction (rootPairCentralizer hij)
        let := MulAction.compHom (X (d + 1)) ψ
        ErgodicSMul H (X (d + 1)) ν := hx
    have hret : ∀ y ∈ K, ∀ h : H, rightAction y ((ψ h).unop : G (d + 1)) ∈ K →
        ∀ g ∈ matrixBall (d + 1) r,
          rightAction y g = rightAction y ((ψ h).unop : G (d + 1)) →
            g ∈ rootPairCentralizer hij := by
      intro y hy h hh g hg heq
      exact hstrong y hy (φ h).toAdd.val (φ h).toAdd.property.1
        (φ h).toAdd.property.2 hh g hg heq
    obtain ⟨z, hz⟩ := rootPair_orbit_of_strong_returns d hij H ψ ν hErg K hK hpos r hr hret
    apply no_neutral_invariant_rootPair_orbit hd hij ν z hz
    intro ell hell hneutral
    exact (hν (Multiplicative.ofAdd (⟨ell, hell, hneutral⟩ : neutralWeightSubgroup i j))).map_eq
  have hcomp : κ ∘ₘ τ = μ := hdec.1
  rw [← hcomp, Measure.bind_apply hK κ.aemeasurable]
  rw [lintegral_congr_ae hzero]
  simp

/-- An almost-everywhere version, so that recurrence null sets may be
removed without changing the mass of the return set. -/
theorem strong_neutral_return_set_null_of_ae
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 < r)
    (hstrong : ∀ᵐ x ∂μ, x ∈ K →
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
      rightAction x (diagonalOneParameter ell hell 1) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
          g ∈ rootPairCentralizer hij) : μ K = 0 := by
  obtain ⟨N, hbad, hN, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hstrong)
  have hKN : μ (K \ N) = 0 := by
    apply strong_neutral_return_set_null d hd hij μ hA (K \ N) (hK.diff hN) r hr
    intro x hx ell hell hn hy g hg heq
    have hxgood : x ∉ {x | ¬ (x ∈ K →
        ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        rightAction x (diagonalOneParameter ell hell 1) ∈ K →
        ∀ g ∈ matrixBall (d + 1) r,
          rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
            g ∈ rootPairCentralizer hij)} := fun h => hx.2 (hbad h)
    exact not_not.mp hxgood hx.1 ell hell hn hy.1 g hg heq
  apply measure_mono_null (show K ⊆ (K \ N) ∪ N by
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, hxN⟩)
  exact measure_union_null hKN hzero

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Arithmetic_ExceptionalSetExclusion
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exclusion of exceptional neutral return sets

A measurable set on which all sufficiently small neutral return lifts
centralize one root has measure zero. The recurrence strengthening makes
these lifts centralize both roots on each quotient chart; the neutral
ergodic decomposition then contradicts the arithmetic orbit obstruction.
This combines the needed directions of EKL (2006), Lemma 4.2,
Proposition 4.3, and Theorem 5.1, without assuming those results.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exceptional_neutral_return_set_null
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K)
    (r : ℝ) (hr : 0 < r)
    (hexceptional : ∀ x ∈ K,
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
      rightAction x (diagonalOneParameter ell hell 1) ∈ K →
      ∀ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) →
          g ∈ singleRootCentralizer hij) : μ K = 0 := by
  choose U hUo hxU R hR hinj using (local_uniform_chart_injective (n := d + 1))
  obtain ⟨S, hSc, hcover⟩ := countable_cover_nhds (fun x => (hUo x).mem_nhds (hxU x))
  have hchart (a : X (d + 1)) : μ (K ∩ U a) = 0 := by
    let q := min r (R a / 2)
    have hq : 0 < q := lt_min hr (half_pos (hR a))
    have hqR : q < R a := lt_of_le_of_lt (min_le_right _ _) (by linarith [hR a])
    have hstrong := ae_strong_returns_on_chart d hij μ hA (rootPairCentralizer hij)
      (fun b => (mem_singleRootCentralizer hij b.val).mpr
        ((mem_rootPairCentralizer hij b.val).mp b.property).1)
      (fun b t => rootPairCentralizer_commutes_contraction hij b.val b.property t)
      q (R a) hq.le hqR (U a) (hUo a).measurableSet (hinj a)
    apply strong_neutral_return_set_null_of_ae d hd hij μ hA
      (K ∩ U a) (hK.inter (hUo a).measurableSet) q hq
    filter_upwards [hstrong] with x hx
    intro hxK ell hell hn hyK g hg heq
    have hgr : g ∈ matrixBall (d + 1) r := fun b c =>
      lt_of_lt_of_le (hg b c) (min_le_left _ _)
    have hgC := hexceptional x hxK.1 ell hell hn hyK.1 g hgr heq
    exact hx hxK.2
      ⟨diagonalOneParameter ell hell 1, diagonal_mem_rootPairCentralizer hij ell hell hn 1⟩
      g hg hgC heq
  apply measure_mono_null (show K ⊆ ⋃ a ∈ S, K ∩ U a by
    intro x hx
    have hxcover : x ∈ ⋃ a ∈ S, U a := by rw [hcover]; trivial
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxcover
    exact mem_iUnion₂.mpr ⟨a, ha, hx, hxa⟩)
  exact (measure_biUnion_null_iff hSc).mpr fun a _ => hchart a

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_NoncentralReturns
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Noncentral neutral return matrices tending to identity

The proved nullity of exceptional return sets supplies arbitrarily small
noncentral lifts on every positive-measure set. Choosing exponentially
shrinking neighborhoods gives the sequence needed for shearing.
Leaf-data equality along the neutral return is not assumed here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_noncentral_neutral_return
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ x ∈ K, ∃ ell : Fin (d + 1) → ℝ, ∃ hell : ∑ a, ell a = 0,
      ell i = ell j ∧ rightAction x (diagonalOneParameter ell hell 1) ∈ K ∧
      ∃ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) ∧
        g ∉ singleRootCentralizer hij := by
  by_contra h
  apply hpos
  apply exceptional_neutral_return_set_null d hd hij μ hA K hK r hr
  intro x hx ell hell hn hy g hg heq
  by_contra hnot
  exact h ⟨x, hx, ell, hell, hn, hy, g, hg, heq, hnot⟩

lemma tendsto_one_of_shrinking_matrixBall
    {n : ℕ} (g : ℕ → G n) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hg : ∀ m, g m ∈ matrixBall n (r m)) : Tendsto g atTop (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun m => abs_nonneg _) (fun m => (hg m a b).le) hr

theorem exists_noncentral_neutral_return_sequence_oai
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ (x y : ℕ → X (d + 1)) (g : ℕ → G (d + 1)),
      Tendsto g atTop (𝓝 1) ∧ ∀ m,
        x m ∈ K ∧ y m ∈ K ∧ rightAction (x m) (g m) = y m ∧
        (¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * g m) ∧
        ∃ ell : Fin (d + 1) → ℝ, ∃ hell : ∑ a, ell a = 0,
          ell i = ell j ∧ rightAction (x m) (diagonalOneParameter ell hell 1) = y m := by
  have hex (m : ℕ) := exists_noncentral_neutral_return d hd hij μ hA K hK hpos
    (Real.exp (-(m : ℝ))) (Real.exp_pos _)
  choose x hx ell hell hn hy g hg heq hnot using hex
  let y : ℕ → X (d + 1) := fun m => rightAction (x m) (diagonalOneParameter (ell m) (hell m) 1)
  refine ⟨x, y, g, ?_, ?_⟩
  · apply tendsto_one_of_shrinking_matrixBall g (fun m => Real.exp (-(m : ℝ))) _ hg
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  · intro m
    refine ⟨hx m, hy m, heq m, ?_, ell m, hell m, hn m, rfl⟩
    intro hc
    exact hnot m ((mem_singleRootCentralizer hij (g m)).mpr (hc 1))

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence_oai := @OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence_oai
