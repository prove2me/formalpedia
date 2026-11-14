-- Prove2me | solution 1 for OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:40.257689+00:00
-- url     : https://prove2.me/submissions/6926046e-22b5-4d4c-b0f2-f189bf173b2e

import Mathlib
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_packet_limit_ball_bound_of_zeta_scale
import Theorems.Thm_OAI_PrimeDegreePackets_positive_entropy_components_ae

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationPreservesVolume _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.euclideanRowBasis_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.OAI.PrimeDegreePackets.rowBasis_apply _root_.infinitePlace_mult_smul
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



lemma map_orbitMap_restrict_eq {d : ℕ} (x : X (d + 1))
    {s t : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain (periodGroup x) s volume)
    (ht : IsAddFundamentalDomain (periodGroup x) t volume) :
    Measure.map (orbitMap x) (volume.restrict s) =
      Measure.map (orbitMap x) (volume.restrict t) := by
  have : Countable (periodGroup x) := countable_of_Lindelof_of_discrete
  ext A hA
  rw [Measure.map_apply (continuous_orbitMap x).measurable hA,
    Measure.map_apply (continuous_orbitMap x).measurable hA,
    Measure.restrict_apply (hA.preimage (continuous_orbitMap x).measurable),
    Measure.restrict_apply (hA.preimage (continuous_orbitMap x).measurable)]
  apply hs.measure_set_eq ht (hA.preimage (continuous_orbitMap x).measurable)
  intro u
  ext v
  change orbitMap x (u.1 + v) ∈ A ↔ orbitMap x v ∈ A
  rw [orbitMap_add, (show orbitMap x u.1 = x from u.property)]

lemma map_orbitMap_add_restrict_eq {d : ℕ} (x : X (d + 1))
    {s : Set (LogCoordinates d)}
    (hs : IsAddFundamentalDomain (periodGroup x) s volume) (u : LogCoordinates d) :
    Measure.map (fun v => orbitMap x (u + v)) (volume.restrict s) =
      Measure.map (orbitMap x) (volume.restrict s) := by
  have htrans := (measurePreserving_add_left (volume : Measure (LogCoordinates d)) u).restrict_image_emb (MeasurableEquiv.addLeft u).measurableEmbedding s
  have ht : IsAddFundamentalDomain (periodGroup x) ((fun v => u + v) '' s) volume :=
    hs.vadd_of_comm u
  calc
    _ = Measure.map (orbitMap x)
        (Measure.map (fun v => u + v) (volume.restrict s)) := by
      have ha : Measurable (fun v : LogCoordinates d => u + v) :=
        measurable_const.add measurable_id
      exact (Measure.map_map (continuous_orbitMap x).measurable ha).symm
    _ = Measure.map (orbitMap x) (volume.restrict ((fun v => u + v) '' s)) := by
      rw [htrans.map_eq]
    _ = _ := map_orbitMap_restrict_eq x ht hs

 

theorem orbitalHaar_invariant {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    Measure.map (fun y => orbitMap y u) (orbitalHaar x) = orbitalHaar x := by
  have hmu : Measurable (fun y => orbitMap y u) :=
    (continuous_rightAction (diagonalFlow u)).measurable
  unfold orbitalHaar
  split_ifs with h
  · rw [Measure.map_map hmu
      (continuous_orbitMap x).measurable]
    have H : (fun y => orbitMap y u) ∘ orbitMap x = fun v => orbitMap x (u + v) := by
      funext v
      rw [Function.comp_apply, ← orbitMap_add, add_comm v u]
    rw [H]
    exact map_orbitMap_add_restrict_eq x h.ExistsIsAddFundamentalDomain.choose_spec u
  · simp

 

theorem orbitProbability_invariant {d : ℕ} (x : X (d + 1)) (u : LogCoordinates d) :
    Measure.map (fun y => orbitMap y u) (orbitProbability x) = orbitProbability x := by
  have hmeas : Measurable (fun y => orbitMap y u) :=
    (continuous_rightAction (diagonalFlow u)).measurable
  simp only [orbitProbability, Measure.map_smul, orbitalHaar_invariant]



theorem packetMeasure_invariant {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d + 1) K) (σ : OrderedEmbeddings (d + 1) K)
    (u : LogCoordinates d) :
    Measure.map (fun x => orbitMap x u) (packetMeasure M σ) = packetMeasure M σ := by
  have hm : Measurable (fun x => orbitMap x u) :=
    (continuous_rightAction (diagonalFlow u)).measurable
  simp only [packetMeasure, Measure.map_smul, Measure.map_sum hm.aemeasurable, orbitProbability_invariant]

open scoped Pointwise



open FractionalIdeal



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
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



theorem right_invariance_of_tendsto {n : ℕ}
    (μ : ℕ → ProbabilityMeasure (X n)) (ν : ProbabilityMeasure (X n))
    (hlim : Tendsto μ atTop (𝓝 ν)) (g : G n)
    (hinv : ∀ i, Measure.map (fun x => rightAction x g) (μ i : Measure (X n)) = μ i) :
    Measure.map (fun x => rightAction x g) (ν : Measure (X n)) = ν := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    μ ν hlim (continuous_rightAction g)
  have heq (i : ℕ) : (μ i).map (f := (fun x => rightAction x g)) (continuous_rightAction g).aemeasurable = μ i := by
    apply Subtype.ext
    exact hinv i
  simp only [heq] at hmap
  have H := tendsto_nhds_unique hmap hlim
  exact congrArg (fun p : ProbabilityMeasure (X n) => (p : Measure (X n))) H



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
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical



theorem packet_limit_diagonal_invariant (d : ℕ) (hodd : Odd (d+1))
    (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν))
    (u : LogCoordinates d) :
    Measure.map (fun x => rightAction x (diagonalFlow u)) (ν : Measure (X (d+1))) = ν := by
  apply right_invariance_of_tendsto _ ν hlim
  intro i
  exact packetMeasure_invariant (M i) (σ i) u

end PrimeDegreePackets

open MeasureTheory Filter Set Module TopologicalSpace
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_KernelEntropy
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets

 

theorem continuous_action_ergodic_decomposition {G Y : Type*} [Group G]
    [TopologicalSpace G] [FirstCountableTopology G] [TopologicalSpace.SeparableSpace G] [TopologicalSpace Y] [mY : MeasurableSpace Y]
    [BorelSpace Y] [HasOuterApproxClosed Y] [StandardBorelSpace Y] [Nonempty Y]
    [MulAction G Y] [ContinuousSMul G Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (hp : ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ) :
    ∃ (m : MeasurableSpace Y) (hm : m ≤ mY),
      letI : MeasurableSpace Y := mY
      condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
        ∀ᵐ x ∂μ.trim hm, ErgodicSMul G Y (condExpKernel μ m x) := by
  obtain ⟨s,hs,hd⟩ := TopologicalSpace.exists_countable_dense G
  let : Countable s := hs.to_subtype
  let H := FreeGroup s
  let «φ» : H →* G := FreeGroup.lift (fun a : s => (a:G))
  have hdφ : DenseRange «φ» := hd.mono (by
    intro g hg
    exact ⟨FreeGroup.of ⟨g,hg⟩,FreeGroup.lift_apply_of⟩)
  let : MulAction H Y := MulAction.compHom Y «φ»
  have hpH (h : H) : MeasurePreserving (fun y : Y => h • y) μ μ := hp («φ» h)
  have hdec := action_ergodic_decomposition μ hpH
  refine ⟨actionInvariantSigma H Y,actionInvariantSigma_le H Y,hdec.1,?_⟩
  filter_upwards [hdec.2] with x hx
  let ν := condExpKernel μ (actionInvariantSigma H Y) x
  let : ErgodicSMul H Y ν := hx
  have hν (g : G) : MeasurePreserving (fun y : Y => g • y) ν ν :=
    preserving_of_dense_action «φ» hdφ ν (fun h =>
      ⟨(hp («φ» h)).measurable,by
        ext B hB
        rw [Measure.map_apply (hp («φ» h)).measurable hB]
        exact SMulInvariantMeasure.measure_preimage_smul h hB⟩) g
  refine { measure_preimage_smul := fun g _ hs => (hν g).measure_preimage hs.nullMeasurableSet
           aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  intro B hB hBfix
  exact ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hB (fun h : H => hBfix («φ» h))

end PrimeDegreePackets

open MeasureTheory Set Topology UniformSpace TopologicalSpace


namespace PrimeDegreePackets



theorem diagonal_positive_ergodic_decomposition (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ)
    (hball : OrdinaryBallBound (d+1) μ) :
    ∃ (m : MeasurableSpace (X (d+1))) (hm : m ≤ xMeasurableSpace (d+1)),
      let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
      condExpKernel μ m ∘ₘ μ.trim hm = μ ∧
      ∀ᵐ z ∂μ.trim hm,
        ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) (condExpKernel μ m z) ∧
        0 < measureEntropy (condExpKernel μ m z)
          (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
            (regularDiagonalWeights_sum d) 1)) := by
  have hp (u : Multiplicative (LogCoordinates d)) :
      MeasurePreserving (fun x : X (d+1) => u • x) μ μ :=
    ⟨(continuous_rightAction _).measurable,hA u.toAdd⟩
  obtain ⟨m,hm,hdec,herg⟩ := continuous_action_ergodic_decomposition μ hp
  let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
  refine ⟨m,hm,hdec,?_⟩
  have hinv : ∀ᵐ z ∂μ.trim hm, ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) (condExpKernel μ m z) =
        condExpKernel μ m z := by
    filter_upwards [herg] with z hz
    let := hz
    intro u
    exact (measurePreserving_smul (Multiplicative.ofAdd u) (condExpKernel μ m z)).map_eq
  have hball' : OrdinaryBallBound (d+1) (condExpKernel μ m ∘ₘ μ.trim hm) := by
    rw [hdec]
    exact hball
  have hprobtrim : @IsProbabilityMeasure (X (d+1)) m (μ.trim hm) := by
    constructor
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_univ
  have hpos := @positive_entropy_components_ae d (X (d+1)) m
    (μ.trim hm) hprobtrim (condExpKernel μ m) inferInstance hball' hinv
  exact herg.and hpos

end PrimeDegreePackets


open scoped ENNReal Topology
namespace PrimeDegreePackets

section Transitive
variable {H Y : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H]
  [MeasurableSpace Y]

 

theorem ae_constant_of_transitive_right_action
    (a : Y → H → Y) (ha : Measurable (fun p : Y × H => a p.1 p.2))
    (hmul : ∀ x g h, a (a x g) h = a x (g*h))
    (htrans : ∀ x y, ∃ g, a x g = y)
    (η : Measure H) [SigmaFinite η] [η.IsMulLeftInvariant] [NeZero η]
    (ρ : Measure Y) [SigmaFinite ρ] [NeZero ρ]
    (f : Y → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ g, (fun x => f (a x g)) =ᵐ[ρ] f) :
    ∃ c : ℝ≥0∞, f =ᵐ[ρ] (fun _ => c) := by
  have hmeas : MeasurableSet {p : Y × H | f (a p.1 p.2) = f p.1} :=
    measurableSet_eq_fun (hf.comp ha) (hf.comp measurable_fst)
  have hall : ∀ᵐ x ∂ρ, ∀ᵐ g ∂η, f (a x g) = f x :=
    (Measure.ae_ae_comm hmeas).mpr (Eventually.of_forall hinv)
  obtain ⟨x,hx⟩ := hall.exists
  refine ⟨f x,hall.mono ?_⟩
  intro y hy
  obtain ⟨g,hg⟩ := htrans x y
  have hshift : ∀ᵐ h ∂η, f (a x (g*h)) = f x :=
    (measurePreserving_mul_left η g).quasiMeasurePreserving.ae hx
  have hxy : ∀ᵐ h ∂η, f (a y h) = f x := by
    simpa only [← hmul,hg] using hshift
  obtain ⟨h,hh₁,hh₂⟩ := (hy.and hxy).exists
  exact hh₁.symm.trans hh₂

 

theorem invariant_probability_unique_transitive
    (a : Y → H → Y) (ha : Measurable (fun p : Y × H => a p.1 p.2))
    (e : H → Y ≃ᵐ Y) (he : ∀ g x, e g x = a x g)
    (hmul : ∀ x g h, a (a x g) h = a x (g*h))
    (htrans : ∀ x y, ∃ g, a x g = y)
    (η : Measure H) [SigmaFinite η] [η.IsMulLeftInvariant] [NeZero η]
    (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ g, Measure.map (fun x => a x g) μ = μ)
    (hν : ∀ g, Measure.map (fun x => a x g) ν = ν) : μ = ν := by
  let ρ := μ+ν
  have hρ : ∀ g, Measure.map (fun x => a x g) ρ = ρ := by
    intro g
    change Measure.map (fun x => a x g) (μ+ν) = μ+ν
    have hg : Measurable (fun x => a x g) :=
      ha.comp (measurable_id.prodMk (measurable_const (a := g)))
    rw [Measure.map_add μ ν hg]
    rw [hμ,hν]
  have : NeZero ρ := ⟨by
    intro h
    have := congrArg (fun m : Measure Y => m Set.univ) h
    simp [ρ] at this⟩
  have Hμ : ∃ c : ℝ≥0∞, μ = c • ρ := by
    have hinv (g : H) : (fun x => μ.rnDeriv ρ (a x g)) =ᵐ[ρ] μ.rnDeriv ρ := by
      have H := (e g).measurableEmbedding.rnDeriv_map μ ρ
      have heq : (e g : Y → Y) = (fun x => a x g) := funext (he g)
      rw [heq,hμ,hρ] at H
      exact H
    obtain ⟨c,hc⟩ := ae_constant_of_transitive_right_action a ha hmul htrans η ρ
      (μ.rnDeriv ρ) (Measure.measurable_rnDeriv _ _) hinv
    refine ⟨c,?_⟩
    rw [← Measure.withDensity_rnDeriv_eq μ ρ (Measure.absolutelyContinuous_of_le (show μ ≤ ρ from Measure.le_add_right le_rfl)),
      withDensity_congr_ae hc,withDensity_const]
  have Hν : ∃ c : ℝ≥0∞, ν = c • ρ := by
    have hinv (g : H) : (fun x => ν.rnDeriv ρ (a x g)) =ᵐ[ρ] ν.rnDeriv ρ := by
      have H := (e g).measurableEmbedding.rnDeriv_map ν ρ
      have heq : (e g : Y → Y) = (fun x => a x g) := funext (he g)
      rw [heq,hν,hρ] at H
      exact H
    obtain ⟨c,hc⟩ := ae_constant_of_transitive_right_action a ha hmul htrans η ρ
      (ν.rnDeriv ρ) (Measure.measurable_rnDeriv _ _) hinv
    refine ⟨c,?_⟩
    rw [← Measure.withDensity_rnDeriv_eq ν ρ (Measure.absolutelyContinuous_of_le (show ν ≤ ρ from Measure.le_add_left le_rfl)),
      withDensity_congr_ae hc,withDensity_const]
  obtain ⟨c,hc⟩ := Hμ
  obtain ⟨b,hb⟩ := Hν
  have hceq : c*(2:ℝ≥0∞) = b*2 := by
    have h₁ := congrArg (fun m : Measure Y => m Set.univ) hc
    have h₂ := congrArg (fun m : Measure Y => m Set.univ) hb
    simp only [measure_univ,Measure.smul_apply,smul_eq_mul,ρ,Measure.add_apply] at h₁ h₂
    have H : (1:ℝ≥0∞)+(1:ℝ≥0∞)=2 := by norm_num
    rw [H] at h₁ h₂
    exact h₁.symm.trans h₂
  have hcb : c=b := (ENNReal.mul_left_inj (show (2:ℝ≥0∞) ≠ 0 by norm_num) (show (2:ℝ≥0∞) ≠ ⊤ by norm_num)).mp hceq
  rw [hc,hb,hcb]

end Transitive
end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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
open MeasureTheory Filter Set

lemma rightAction_transitive (n : ℕ) (x y : X n) : ∃ g : G n, rightAction x g = y := by
  obtain ⟨a,rfl⟩ := Quotient.exists_rep x
  obtain ⟨b,rfl⟩ := Quotient.exists_rep y
  refine ⟨a⁻¹*b,?_⟩
  change Quotient.mk _ (a*(a⁻¹*b)) = Quotient.mk _ b
  simp

 

theorem isHaarProbability_unique {n : ℕ} {μ ν : Measure (X n)}
    (hμ : IsHaarProbability μ) (hν : IsHaarProbability ν) : μ = ν := by
  let : MeasurableSpace (G n) := borel (G n)
  let : BorelSpace (G n) := ⟨rfl⟩
  have : IsProbabilityMeasure μ := hμ.1
  have : IsProbabilityMeasure ν := hν.1
  exact invariant_probability_unique_transitive (@rightAction n)
    (continuous_rightAction_uncurry n).measurable
    (fun g => (rightActionHomeomorph g).toMeasurableEquiv) (fun _ _ => rfl)
    (fun x g h => rightAction_mul x g h) (rightAction_transitive n)
    (Measure.haar : Measure (G n)) μ ν hμ.2 hν.2

end PrimeDegreePackets


namespace PrimeDegreePackets



open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators



theorem packet_limit_positive_ergodic_components_of_zeta_scale
    (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν)) :
    ∃ (m : MeasurableSpace (X (d+1))) (hm : m ≤ xMeasurableSpace (d+1)),
      let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
      condExpKernel (ν : Measure (X (d+1))) m ∘ₘ (ν : Measure (X (d+1))).trim hm = ν ∧
      ∀ᵐ z ∂(ν : Measure (X (d+1))).trim hm,
        ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1))
          (condExpKernel (ν : Measure (X (d+1))) m z) ∧
        0 < measureEntropy (condExpKernel (ν : Measure (X (d+1))) m z)
          (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
            (regularDiagonalWeights_sum d) 1)) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  apply diagonal_positive_ergodic_decomposition d ν
  · exact packet_limit_diagonal_invariant d hodd K M σ hn ν hlim
  · intro Ω hΩ
    exact packet_limit_ball_bound_of_zeta_scale d hodd Hscale K M σ hn hQ ν hlim hΩ

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaDerivatives
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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

 

theorem haar_barycenter {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (κ : Kernel Y (X n)) [IsMarkovKernel κ]
    (m : Measure (X n)) (hm : IsHaarProbability m)
    (hinv : ∀ᵐ y ∂μ, ∀ g : G n, Measure.map (fun x => rightAction x g) (κ y) = κ y) :
    κ ∘ₘ μ = m := by
  have heq : ∀ᵐ y ∂μ, κ y = (Kernel.const Y m) y := by
    filter_upwards [hinv] with y hy
    exact isHaarProbability_unique ⟨(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),hy⟩ hm
  rw [Measure.comp_congr heq,Measure.const_comp,measure_univ,one_smul]

 

theorem measure_eq_haar_of_condExpKernel_invariance {n : ℕ}
    (ν : Measure (X n)) [IsProbabilityMeasure ν]
    (m : Measure (X n)) (hm : IsHaarProbability m)
    (s : MeasurableSpace (X n)) (hs : s ≤ xMeasurableSpace n) :
    let : MeasurableSpace (X n) := xMeasurableSpace n
    condExpKernel ν s ∘ₘ ν.trim hs = ν →
    (∀ᵐ y ∂ν.trim hs, ∀ g : G n,
      Measure.map (fun x => rightAction x g) (condExpKernel ν s y) = condExpKernel ν s y) →
    ν = m := by
  dsimp only
  let : MeasurableSpace (X n) := xMeasurableSpace n
  intro hdec hinv
  have hp : @IsProbabilityMeasure (X n) s (ν.trim hs) := by
    constructor
    rw [trim_measurableSet_eq hs (@MeasurableSet.univ _ s)]
    exact measure_univ
  exact hdec.symm.trans (@haar_barycenter (X n) s n (ν.trim hs) hp
    (condExpKernel ν s) inferInstance m hm hinv)

end PrimeDegreePackets

open MeasureTheory Filter Set Matrix
open scoped Topology Classical
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_MainConditional
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Conditional prime-degree packet equidistribution

Complete volume-weighted local-homothety packets converge to Haar
probability and form a tight family under a residue-relative uniform
zeta scale bound and prime-degree positive-entropy rigidity. The
arithmetic and dynamical hypotheses concern the actual homogeneous
lattice space and its diagonal action. A subsequential packet limit
supplies Haar probability.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

/-- Every weak packet limit is Haar under the analytic scale bound and
published prime-degree rigidity. -/
theorem packet_limit_isHaar_of_scale_and_EKL_oai
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hthree : 3 ≤ d + 1) (hodd : Odd (d + 1))
    (Hscale : UniformZetaScaleBound.{u} (d + 1)) (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d + 1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd)
      atTop (𝓝 ν)) : IsHaarProbability (ν : Measure (X (d + 1))) := by
  obtain ⟨m, hm, hdec, hcomp⟩ :=
    packet_limit_positive_ergodic_components_of_zeta_scale d hodd Hscale K M σ hn hD ν hlim
  let : MeasurableSpace (X (d + 1)) := xMeasurableSpace (d + 1)
  let : @IsProbabilityMeasure (X (d + 1)) m
      ((ν : Measure (X (d + 1))).trim hm) := by
    constructor
    rw [trim_measurableSet_eq hm (@MeasurableSet.univ _ m)]
    exact measure_univ
  have hHaar : ∀ᵐ z ∂(ν : Measure (X (d + 1))).trim hm,
      IsHaarProbability (condExpKernel (ν : Measure (X (d + 1))) m z) := by
    filter_upwards [hcomp] with z hz
    exact ekl hprime hthree _ inferInstance hz.1 hz.2
  obtain ⟨z, hz⟩ := hHaar.exists
  have heq := measure_eq_haar_of_condExpKernel_invariance
    (ν : Measure (X (d + 1)))
    (condExpKernel (ν : Measure (X (d + 1))) m z) hz m hm hdec
    (hHaar.mono fun _ h => h.2)
  exact heq.symm ▸ hz

end DukePrimeDegree

end OAI
end

theorem solution.{u} : type_of% @OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL_oai.{u} := @OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL_oai.{u}
