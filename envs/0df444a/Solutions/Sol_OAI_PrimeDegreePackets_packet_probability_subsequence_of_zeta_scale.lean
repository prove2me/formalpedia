-- Prove2me | solution 1 for OAI.PrimeDegreePackets.packet_probability_subsequence_of_zeta_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:44.345683+00:00
-- url     : https://prove2.me/submissions/9c37e37d-1334-4dd5-a324-6edad3054045

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_packet_tight_of_zeta_scale

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
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
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors



lemma integralElements_scaled_index {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : Module.finrank ℚ K = n) (q : ℕ) :
    ((integralElements K).map (nsmulAddMonoidHom q)).relIndex (integralElements K) = q ^ n := by
  let e : 𝓞 K ≃+ (integralElements K).toIntSubmodule := AddEquiv.refl _
  let : Module.Free ℤ (integralElements K).toIntSubmodule :=
    Module.Free.of_equiv e.toIntLinearEquiv
  let : Module.Finite ℤ (integralElements K).toIntSubmodule :=
    Module.Finite.equiv e.toIntLinearEquiv
  rw [AddSubgroup.relIndex_map_nsmul]
  congr 1
  exact e.toIntLinearEquiv.finrank_eq.symm.trans ((NumberField.RingOfIntegers.rank K).trans hn)

 

theorem multiplierOrder_index_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    (multiplierOrder M).relIndex (integralElements K) ≤ saturationIndex M ^ n := by
  have h := AddSubgroup.relIndex_le_of_le_left
    (scaled_integralElements_le_multiplierOrder M)
    (show ((integralElements K).map (nsmulAddMonoidHom (saturationIndex M))).relIndex
      (integralElements K) ≠ 0 by
        rw [integralElements_scaled_index hn]
        exact pow_ne_zero _ (saturationIndex_ne_zero M))
  rwa [integralElements_scaled_index hn] at h



lemma fieldDiscriminant_one_le (K : Type*) [Field K] [NumberField K] :
    1 ≤ |(NumberField.discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

lemma packetScale_pos {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : 0 < packetScale M := by
  unfold packetScale
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M))
    (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (fieldDiscriminant_one_le K)))

 

theorem multiplierDiscriminant_le_packetScale_pow {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (hnpos : 0 < n) : multiplierDiscriminant M ≤ packetScale M ^ (2 * n) := by
  have hi : ((multiplierOrder M).relIndex (integralElements K) : ℝ) ≤
      (saturationIndex M : ℝ) ^ n := by exact_mod_cast multiplierOrder_index_le M hn
  have hD := fieldDiscriminant_one_le K
  have hDp : |(NumberField.discr K : ℝ)| ≤ |(NumberField.discr K : ℝ)| ^ n :=
    le_self_pow₀ hD hnpos.ne'
  calc
    multiplierDiscriminant M ≤ |(NumberField.discr K : ℝ)| *
        ((saturationIndex M : ℝ) ^ n) ^ 2 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 2) (abs_nonneg _)
    _ ≤ |(NumberField.discr K : ℝ)| ^ n * ((saturationIndex M : ℝ) ^ n) ^ 2 :=
      mul_le_mul_of_nonneg_right hDp (sq_nonneg _)
    _ = packetScale M ^ (2 * n) := by
      unfold packetScale
      rw [mul_pow, pow_mul (Real.sqrt _) 2 n, Real.sq_sqrt (abs_nonneg _),
        ← pow_mul, Nat.mul_comm n 2, mul_comm]

 

theorem packetScale_tendsto_of_multiplierDiscriminant_tendsto
    {n : ℕ} (hnpos : 0 < n) (K : ℕ → Type*)
    [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    (M : ∀ i, FullLattice n (K i)) (hn : ∀ i, Module.finrank ℚ (K i) = n)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop) :
    Tendsto (fun i => packetScale (M i)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hD.eventually (eventually_gt_atTop (|b| ^ (2 * n)))] with i hi
  have hlt : |b| ^ (2 * n) < packetScale (M i) ^ (2 * n) :=
    hi.trans_le (multiplierDiscriminant_le_packetScale_pow (M i) (hn i) hnpos)
  by_contra hb
  have hle : packetScale (M i) ≤ |b| := (le_of_not_ge hb).trans (le_abs_self b)
  exact (not_lt_of_ge (pow_le_pow_left₀ (packetScale_pos (M i)).le hle _)) hlt



open scoped Pointwise



open FractionalIdeal



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets



open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators


theorem packet_probability_subsequence_of_zeta_scale_oai (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop) :
    ∃ (ν : ProbabilityMeasure (X (d+1))) («φ» : ℕ → ℕ), StrictMono «φ» ∧
      Tendsto (fun i => packetProbability (M («φ» i)) (σ («φ» i)) (hn («φ» i)) hodd)
        atTop (𝓝 ν) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  have htight := packet_tight_of_zeta_scale d hodd Hscale K M σ hn hQ
  let p := fun i => packetProbability (M i) (σ i) (hn i) hodd
  have ht : IsTightMeasureSet {((μ : ProbabilityMeasure (X (d+1))) : Measure (X (d+1))) |
      μ ∈ Set.range p} := by
    convert htight using 1
    all_goals try with_reducible_and_instances rfl
    ext μ
    simp only [Set.mem_ofPred_eq,Set.mem_range]
    constructor
    · rintro ⟨ν,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨p i,⟨i,rfl⟩,rfl⟩
  obtain ⟨ν,_,«φ»,hφ,hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
      (fun i => subset_closure (Set.mem_range_self i))
  exact ⟨ν,«φ»,hφ,hlim⟩



end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.PrimeDegreePackets.packet_probability_subsequence_of_zeta_scale_oai.{u} := @OAI.PrimeDegreePackets.packet_probability_subsequence_of_zeta_scale_oai.{u}
