-- Prove2me | solution 1 for OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:55:12.113206+00:00
-- url     : https://prove2.me/submissions/afceaf50-b3fe-45bd-a102-65cd1a656e83

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_global_local_weight_moment_of_support_prod_le

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets

section Algebra
variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]


lemma productDVRShell_transitive (k : ι → ℕ) {x y : ∀ i, R i}
    (hx : x ∈ productDVRShell R k) (hy : y ∈ productDVRShell R k) :
    ∃ u : (∀ i, R i)ˣ, u • x = y := by
  have h (i : ι) : Associated (x i) (y i) :=
    (addVal_eq_iff_associated _ _).mp ((hx i).trans (hy i).symm)
  choose u hu using h
  refine ⟨MulEquiv.piUnits.symm u, ?_⟩
  funext i
  change (u i : R i) * x i = y i
  simpa only [mul_comm] using hu i

end Algebra

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets

open scoped NumberField Pointwise nonZeroDivisors
open NumberField


lemma local_relIndex_smul
    {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (c : (LocalAlgebra p K)ˣ) (L R : Submodule (PadicInt p) (LocalAlgebra p K)) :
    ((c : LocalAlgebra p K) • L).toAddSubgroup.relIndex
      ((c : LocalAlgebra p K) • R).toAddSubgroup = L.toAddSubgroup.relIndex R.toAddSubgroup := by
  exact AddSubgroup.relIndex_pointwise_smul c L.toAddSubgroup R.toAddSubgroup

lemma saturation_completed_primePower_mem
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] {x : LocalAlgebra p K}
    (hx : x ∈ completedFractionalIdeal p (saturationFractionalIdeal M)) :
    (p : PadicInt p)^((saturationIndex M).factorization p) • x ∈ completedLattice p M := by
  apply completedLattice_primePower_mem (M := fractionalIdealFullLattice hn (saturationIdealUnit M))
    (saturationIndex M) _ p _ (ordCompl[p] (saturationIndex M))
    (Nat.ordProj_mul_ordCompl_eq_self (saturationIndex M) p).symm
    (Nat.coprime_ordCompl Fact.out (saturationIndex_ne_zero M)) hx
  intro y hy
  exact_mod_cast saturationIndex_smul_mem M hy

lemma saturation_completed_eq_off
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ saturationIndex M) :
    completedLattice p M = completedFractionalIdeal p (saturationFractionalIdeal M) := by
  apply le_antisymm
  · exact completedLattice_mono (M := M)
      (N := fractionalIdealFullLattice hn (saturationIdealUnit M)) (le_saturation M) p
  · intro x hx
    have H := saturation_completed_primePower_mem M hn p hx
    simpa only [Nat.factorization_eq_zero_of_not_dvd hp,pow_zero,one_smul] using H

 
theorem saturationIndex_eq_prod_local
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    saturationIndex M = ∏ p : labelPrimes M,
      (completedLattice p.val M).toAddSubgroup.relIndex
        (completedFractionalIdeal p.val (saturationFractionalIdeal M)).toAddSubgroup := by
  apply fullLattice_relIndex_eq_prod_local (fractionalIdealFullLattice hn (saturationIdealUnit M)) M hn
    (fun p : labelPrimes M => p.val) Subtype.val_injective
    (fun p => (saturationIndex M).factorization p.val)
    (fun p x hx => saturation_completed_primePower_mem M hn p.val hx)
  intro p hp hnot
  let : Fact p.Prime := ⟨hp⟩
  apply saturation_completed_eq_off M hn p
  intro hd
  exact hnot ⟨⟨p,Nat.mem_primeFactors.mpr ⟨hp,hd,saturationIndex_ne_zero M⟩⟩,rfl⟩



open Topology
open scoped Pointwise

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


lemma ideal_span_comap_top_of_mul {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (A : Subalgebra R B) (L : Submodule R B) (hL : L ≤ A.toSubmodule)
    (hsat : A.toSubmodule * L = A.toSubmodule) :
    Ideal.span ((L.comap A.val.toLinearMap) : Set A) = ⊤ := by
  let J := Ideal.span ((L.comap A.val.toLinearMap) : Set A)
  have hmul : A.toSubmodule * L ≤ (J.restrictScalars R).map A.val.toLinearMap := by
    apply Submodule.mul_le.mpr
    intro a ha b hb
    refine ⟨(⟨a,ha⟩ : A) * ⟨b,hL hb⟩, ?_, rfl⟩
    exact J.mul_mem_left _ (Ideal.subset_span hb)
  rw [hsat] at hmul
  obtain ⟨x,hx,hxv⟩ := hmul (show (1 : B) ∈ A.toSubmodule from A.one_mem)
  apply (Ideal.eq_top_iff_one _).mpr
  have hx1 : x = 1 := Subtype.ext hxv
  exact hx1 ▸ hx

 
lemma ideal_span_map_equiv_top {S R T : Type*} [CommRing S] [CommRing R] [CommRing T]
    [Algebra S R] [Algebra S T] (e : R ≃ₐ[S] T)
    (L : Submodule S R) (hL : Ideal.span (L : Set R) = ⊤) :
    Ideal.span (L.map e.toLinearMap : Set T) = ⊤ := by
  rw [Submodule.map_coe]
  change Ideal.span (e.toRingHom '' (L : Set R)) = ⊤
  rw [← Ideal.map_span, hL, Ideal.map_top]

lemma integralNormalizedModule_saturated {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    Ideal.span (integralNormalizedModule M p : Set (completedMaximalOrder (K := K) p)) = ⊤ :=
  ideal_span_comap_top_of_mul _ _ (normalizedLocalModule_le M p)
    (normalizedLocalModule_saturation M p)

lemma integralNormalizedModule_open {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsOpen (integralNormalizedModule M p : Set (completedMaximalOrder (K := K) p)) := by
  change IsOpen (Subtype.val ⁻¹' (normalizedLocalModule M p : Set (LocalAlgebra p K)))
  apply IsOpen.preimage continuous_subtype_val
  unfold normalizedLocalModule
  rw [Submodule.coe_pointwise_smul]
  exact (completedLattice_open M hn p).smul (idealLocalGenerator p (saturationIdealUnit M))⁻¹

lemma integralNormalizedModule_finiteQuotient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    Finite (completedMaximalOrder (K := K) p ⧸ integralNormalizedModule M p) :=
  AddSubgroup.quotient_finite_of_isOpen (integralNormalizedModule M p).toAddSubgroup
    (integralNormalizedModule_open M hn p)

lemma integralNormalizedModule_cardQuot {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime] :
    (integralNormalizedModule M p).cardQuot =
      (completedLattice p M).toAddSubgroup.relIndex
        (completedFractionalIdeal p (saturationFractionalIdeal M)).toAddSubgroup := by
  change (normalizedLocalModule M p).toAddSubgroup.relIndex
    (completedMaximalOrder (K := K) p).toSubmodule.toAddSubgroup = _
  have H := local_relIndex_smul p (idealLocalGenerator p (saturationIdealUnit M))⁻¹
    (completedLattice p M) (completedFractionalIdeal p (saturationFractionalIdeal M))
  rw [saturationLocalGenerator_spec, ← mul_smul, Units.inv_mul, one_smul] at H
  rw [saturationLocalGenerator_spec]
  exact H

lemma saturationIndex_eq_prod_integralNormalizedModule {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    saturationIndex M = ∏ p : labelPrimes M, (integralNormalizedModule M p.val).cardQuot := by
  apply (saturationIndex_eq_prod_local M hn).trans
  apply Finset.prod_congr rfl
  intro p _
  exact (integralNormalizedModule_cardQuot M p.val).symm



lemma modelLocalModule_saturated {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) :
    Ideal.span (modelLocalModule M p E : Set R) = ⊤ :=
  ideal_span_map_equiv_top E _ (integralNormalizedModule_saturated M p)

lemma modelLocalModule_open {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R] [TopologicalSpace R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) (hE : Continuous E.symm) :
    IsOpen (modelLocalModule M p E : Set R) := by
  rw [modelLocalModule, Submodule.map_equiv_eq_comap_symm E.toLinearEquiv]
  exact (integralNormalizedModule_open M hn p).preimage hE

lemma modelLocalModule_finiteQuotient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) :
    Finite (R ⧸ modelLocalModule M p E) := by
  let := integralNormalizedModule_finiteQuotient M hn p
  exact Finite.of_equiv _ (Submodule.Quotient.equiv _ _ E.toLinearEquiv rfl).toEquiv

lemma modelLocalModule_cardQuot {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) :
    (modelLocalModule M p E).cardQuot = (integralNormalizedModule M p).cardQuot :=
  cardQuot_map_equiv E.toLinearEquiv _

open MeasureTheory
open scoped ENNReal

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_OrbitProbability
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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


namespace PrimeDegreePackets

section Action
variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]



omit [MeasurableMul G] [IsProbabilityMeasure ν] [ν.IsMulRightInvariant] in
lemma orbitContainmentProbability_eq_measure (L : Set X) (hL : MeasurableSet L) (x : X) :
    orbitContainmentProbability ν L x = ν {g : G | g • x ∈ L} := by
  unfold orbitContainmentProbability
  have heq : (fun (g : G) => L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) =
      {g : G | g • x ∈ L}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    rfl
  rw [heq]
  exact lintegral_indicator_fun_one (hL.preimage (measurable_id.smul_const x))

omit [MeasurableSpace X] [MeasurableSMul₂ G X] [IsProbabilityMeasure ν] in
lemma orbitContainmentProbability_smul (L : Set X) (x : X) (g : G) :
    orbitContainmentProbability ν L (g • x) = orbitContainmentProbability ν L x := by
  unfold orbitContainmentProbability
  simp_rw [← mul_smul]
  exact lintegral_mul_right_eq_self (fun h => L.indicator (fun _ => (1 : ℝ≥0∞)) (h • x)) g



end Action
end PrimeDegreePackets


open Filter
open scoped BigOperators Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.model_units_measurableSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators


lemma localProductConstant_pos (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < localProductConstant n ε hε :=
  (localMajorant_product_le n ε hε).choose_spec.1

end PrimeDegreePackets


namespace PrimeDegreePackets

 

lemma reciprocal_norm_tail_le {α : Type*} (w d : α → ℝ≥0∞)
    (hd0 : ∀ i, d i ≠ 0) (hdt : ∀ i, d i ≠ ∞)
    (T : ℝ≥0∞) (s : ℝ) (hs : 0 ≤ s) :
    (∑' i, if T < d i then w i / d i else 0) ≤
      T ^ (-s) * ∑' i, w i * d i ^ (s - 1) := by
  classical
  calc
    _ ≤ ∑' i, T ^ (-s) * (w i * d i ^ (s - 1)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      split_ifs with h
      · have hp : d i ^ (-s) ≤ T ^ (-s) := by
          simp only [ENNReal.rpow_neg, ENNReal.inv_le_inv]
          exact ENNReal.rpow_le_rpow h.le hs
        calc
          w i / d i = d i ^ (-s) * (w i * d i ^ (s - 1)) := by
            rw [mul_left_comm, ← ENNReal.rpow_add _ _ (hd0 i) (hdt i)]
            simp [show -s + (s - 1) = -1 by ring, ENNReal.rpow_neg_one, div_eq_mul_inv]
          _ ≤ _ := mul_le_mul_left hp _
      · exact bot_le
    _ = _ := ENNReal.tsum_mul_left

 

lemma reciprocal_norm_tail_of_moment {α : Type*} (w d : α → ℝ≥0∞)
    (hd0 : ∀ i, d i ≠ 0) (hdt : ∀ i, d i ≠ ∞)
    (q Q C : ℝ≥0∞) (hQ0 : Q ≠ 0) (hQt : Q ≠ ∞) (hqQ : q ≤ Q)
    (s : ℝ) (hs : 0 < s)
    (hm : (∑' i, w i * d i ^ (s - 1)) ≤ q⁻¹ * C * q ^ (s / 16)) :
    (∑' i, if Q ^ (1 / 8 : ℝ) < d i then w i / d i else 0) ≤
      q⁻¹ * C * Q ^ (-s / 16) := by
  classical
  calc
    _ ≤ (Q ^ (1 / 8 : ℝ)) ^ (-s) * ∑' i, w i * d i ^ (s - 1) :=
      reciprocal_norm_tail_le w d hd0 hdt _ s hs.le
    _ ≤ (Q ^ (1 / 8 : ℝ)) ^ (-s) * (q⁻¹ * C * q ^ (s / 16)) :=
      mul_le_mul_right hm _
    _ ≤ (Q ^ (1 / 8 : ℝ)) ^ (-s) * (q⁻¹ * C * Q ^ (s / 16)) := by
      exact mul_le_mul_right (mul_le_mul_right (ENNReal.rpow_le_rpow hqQ (by positivity)) _) _
    _ = q⁻¹ * C * Q ^ (-s / 16) := by
      rw [← ENNReal.rpow_mul, mul_left_comm,
        ← ENNReal.rpow_add _ _ hQ0 hQt]
      congr 2
      ring

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory NumberField IsDiscreteValuationRing
open scoped ENNReal Pointwise nonZeroDivisors



lemma modelUnitProbability_isProbability {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) (hE : Continuous E) :
    IsProbabilityMeasure (modelUnitProbability p E) := by
  apply (Measure.isProbabilityMeasure_map_iff
    (Units.continuous_map hE).measurable.aemeasurable).mpr
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma modelUnitProbability_isHaar {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R) (hE : Continuous E) :
    (modelUnitProbability p E).IsHaarMeasure := by
  exact Measure.isHaarMeasure_map_of_isFiniteMeasure (localUnitHaarProbability p)
    (Units.mapEquiv E.toMulEquiv).toMonoidHom (Units.continuous_map hE)
    (Units.mapEquiv E.toMulEquiv).surjective

lemma smul_normalized_mem_iff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (u : completedMaximalOrder (K := K) p) (z : (completedMaximalOrder (K := K) p)ˣ) :
    (u : LocalAlgebra p K) ∈ ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
      normalizedLocalModule M p ↔ z⁻¹ • u ∈ integralNormalizedModule M p := by
  let v : (LocalAlgebra p K)ˣ :=
    Units.map (completedMaximalOrder (K := K) p).val.toMonoidHom z
  change (u : LocalAlgebra p K) ∈ v • (normalizedLocalModule M p : Set (LocalAlgebra p K)) ↔ _
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

 

lemma actual_containment_eq_model_orbit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra (PadicInt p) R]
    [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] R)
    (hE : Continuous E) (hEs : Continuous E.symm)
    (u : completedMaximalOrder (K := K) p) :
    localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
      (u : LocalAlgebra p K) ∈ ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
        normalizedLocalModule M p} =
      orbitContainmentProbability (modelUnitProbability p E) (modelLocalModule M p E) (E u) := by
  rw [orbitContainmentProbability_eq_measure _ _ (modelLocalModule_open M hn p E hEs).measurableSet]
  have hm : Measurable (Units.mapEquiv E.toMulEquiv) :=
    (Units.continuous_map (f := E.toMonoidHom) hE).measurable
  have hset : MeasurableSet {z : Rˣ | z • E u ∈ modelLocalModule M p E} :=
    (modelLocalModule_open M hn p E hEs).measurableSet.preimage (measurable_id.smul_const _)
  change _ = (modelUnitProbability p E) {z : Rˣ | z • E u ∈ modelLocalModule M p E}
  unfold modelUnitProbability
  rw [Measure.map_apply hm hset]
  have he : (Units.mapEquiv E.toMulEquiv) ⁻¹' {z : Rˣ | z • E u ∈ modelLocalModule M p E} =
      {z : (completedMaximalOrder (K := K) p)ˣ | z • u ∈ integralNormalizedModule M p} := by
    ext z
    change E (z : completedMaximalOrder (K := K) p) * E u ∈
      (integralNormalizedModule M p).map E.toLinearMap ↔ _
    rw [← map_mul E]
    rw [Submodule.mem_map_equiv]
    change E.symm (E ((z : completedMaximalOrder (K := K) p) * u)) ∈
      integralNormalizedModule M p ↔ _
    rw [E.symm_apply_apply]
    rfl
  rw [he]
  have hi := Measure.measure_preimage_inv (localUnitHaarProbability (K := K) p)
    {z : (completedMaximalOrder (K := K) p)ˣ | z • u ∈ integralNormalizedModule M p}
  rw [← hi]
  congr 1
  ext z
  exact smul_normalized_mem_iff M p u z



theorem localIdealWeight_eq_model_shell {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, Algebra (PadicInt p) (R i)] [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)] [∀ i, SecondCountableTopology (R i)] [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] ∀ i, R i)
    (hE : Continuous E) (hEs : Continuous E.symm)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    localIdealWeight M p J = localShellProbability R (modelUnitProbability p E)
      (modelLocalModule M p E)
      (fun i => (addVal (R i) (E ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩ i)).toNat) := by
  let u : completedMaximalOrder (K := K) p :=
    ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩
  let k : ι → ℕ := fun i => (addVal (R i) (E u i)).toNat
  let := modelUnitProbability_isProbability p E hE
  let := modelUnitProbability_isHaar p E hE
  have hxu : E u ∈ productDVRShell R k := by
    intro i
    exact (ENat.natCast_toNat (addVal_eq_top_iff.not.mpr
      (model_generator_components_ne_zero p E _ _ i))).symm
  obtain ⟨z,hz⟩ := productDVRShell_transitive R k
    (productDVRShell_nonempty R k).choose_spec hxu
  change localIdealWeight M p J = orbitContainmentProbability (modelUnitProbability p E)
    (modelLocalModule M p E) (productDVRShell_nonempty R k).choose
  rw [localIdealWeight, actual_containment_eq_model_orbit M hn p E hE hEs u, ← hz]
  exact orbitContainmentProbability_smul (modelUnitProbability p E)
    (modelLocalModule M p E : Set (∀ i, R i)) _ z

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalModels
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators



instance model_actual_unit_probability {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    IsProbabilityMeasure (modelUnitProbability p T.equiv) :=
  modelUnitProbability_isProbability p T.equiv T.continuous_equiv

instance model_actual_unit_haar {p : ℕ} [Fact p.Prime] {K : Type u}
    [Field K] [NumberField K] (T : ActualLocalModel p K) :
    (modelUnitProbability p T.equiv).IsHaarMeasure :=
  modelUnitProbability_isHaar p T.equiv T.continuous_equiv



theorem actual_tuple_weight_moment {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    (∑' k, actualTupleWeight M k * actualTupleNorm M k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (saturationIndex M : ℝ) ^ ε) := by
  let T (p : labelPrimes M) := actualLocalModel p.val K
  let L (p : labelPrimes M) := modelLocalModule M p.val (T p).equiv
  let (p : labelPrimes M) : Finite ((∀ i, (T p).Ring i) ⧸ L p) :=
    modelLocalModule_finiteQuotient M hn p.val (T p).equiv
  have hq : localIndexProduct (saturationIndex M).primeFactors (fun p => (T p).Index)
      (fun p => (T p).Ring) L = saturationIndex M := by
    unfold localIndexProduct
    dsimp only [L]
    simp_rw [modelLocalModule_cardQuot]
    exact (saturationIndex_eq_prod_integralNormalizedModule M hn).symm
  have hprod : (∏ p ∈ (saturationIndex M).primeFactors, (p : ℝ)) ≤
      (localIndexProduct (saturationIndex M).primeFactors (fun p => (T p).Index)
        (fun p => (T p).Ring) L : ℝ) := by
    rw [hq, ← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (saturationIndex_ne_zero M))
      (Nat.prod_primeFactors_dvd (saturationIndex M))
  have H := global_local_weight_moment_of_support_prod_le n (saturationIndex M).primeFactors
    (fun p => (T p).Index) (fun p => (T p).Ring)
    (fun p => modelAddHaarProbability (T p)) (fun p => modelUnitProbability p.val (T p).equiv)
    L hn0 ε hε
    (fun p => (modelLocalModule_open M hn p.val (T p).equiv (T p).continuous_symm).measurableSet)
    hprod (fun p => modelLocalModule_saturated M p.val (T p).equiv)
    (fun p => (T p).e) (fun p => (T p).f) (fun p => (T p).e_pos)
    (fun p => (T p).f_pos) (fun p => (T p).valuation_p)
    (fun p => (T p).card_residue) (fun p => (T p).degree.trans hn)
  rw [hq] at H
  exact H

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal


theorem integralIdeal_norm_eq_valuation_product {K : Type*} [Field K] [NumberField K]
    (J : {I : Ideal (𝓞 K) // I ≠ ⊥}) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (hsupp : ∀ p, p.Prime → p ∣ Ideal.absNorm J.1 → p ∈ S)
    (T : ∀ p : S, ActualLocalModel p.val K) :
    Ideal.absNorm J.1 =
      ∏ p : S, ∏ i, p.val ^ ((T p).f i *
        integralIdealValuations p.val (T p) (nonzeroIntegralIdealUnit J)
          (nonzeroIntegralIdealUnit_le_one J) i) := by
  let U := nonzeroIntegralIdealUnit J
  have H := fullLattice_relIndex_eq_prod_local
    (fractionalIdealFullLattice (n := Module.finrank ℚ K) rfl 1)
    (fractionalIdealFullLattice rfl U) rfl (fun p : S => p.val) Subtype.val_injective
    (fun p => (Ideal.absNorm J.1).factorization p.val)
    (fun p _ hx => completed_ideal_primePower_mem J p.val hx)
    (by
      intro p hp
      let : Fact p.Prime := ⟨hp⟩
      intro hnot
      exact completed_ideal_eq_off J p (fun hdiv => hnot ⟨⟨p,hsupp p hp hdiv⟩,rfl⟩))
  rw [fullLattice_ideal_relIndex] at H
  apply H.trans
  apply Finset.prod_congr rfl
  intro p _
  change (completedFractionalIdeal p.val (U : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup.relIndex
    (completedFractionalIdeal p.val (1 : FractionalIdeal (𝓞 K)⁰ K)).toAddSubgroup = _
  rw [← integralCompletedIdeal_relIndex]
  exact integralCompletedIdeal_cardQuot p.val (T p) U (nonzeroIntegralIdealUnit_le_one J)


lemma primaryIdeal_actual_weight {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (J : primaryIntegralIdeals K (saturationIndex M).primeFactors) :
    globalIdealWeight M (nonzeroIntegralIdealUnit J.1) =
      actualTupleWeight M (primaryIdealValuations (saturationIndex M).primeFactors
        (fun p => actualLocalModel p.val K) J) := by
  apply Finset.prod_congr rfl
  intro p _
  exact localIdealWeight_eq_model_shell M hn p.val (actualLocalModel p.val K).Ring
    (actualLocalModel p.val K).equiv (actualLocalModel p.val K).continuous_equiv
    (actualLocalModel p.val K).continuous_symm _ (nonzeroIntegralIdealUnit_le_one J.1)

lemma primaryIdeal_actual_norm {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : primaryIntegralIdeals K (saturationIndex M).primeFactors) :
    (Ideal.absNorm J.1.1 : ℝ≥0∞) =
      actualTupleNorm M (primaryIdealValuations (saturationIndex M).primeFactors
        (fun p => actualLocalModel p.val K) J) := by
  rw [integralIdeal_norm_eq_valuation_product J.1 _ J.2 (fun p => actualLocalModel p.val K)]
  simp only [Nat.cast_prod, Nat.cast_pow, actualTupleNorm, shellNorm]
  apply Finset.prod_congr rfl
  intro p _
  apply Finset.prod_congr rfl
  intro i _
  rw [(actualLocalModel p.val K).card_residue, Nat.cast_pow, pow_mul]
  rfl



theorem primaryIdeal_moment_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    (∑' J : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      globalIdealWeight M (nonzeroIntegralIdealUnit J.1) *
        (Ideal.absNorm J.1.1 : ℝ≥0∞) ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (localProductConstant n ε hε * (saturationIndex M : ℝ) ^ ε) := by
  simp_rw [primaryIdeal_actual_weight M hn, primaryIdeal_actual_norm M]
  apply (ENNReal.tsum_comp_le_tsum_of_injective
    (primaryIdealValuations_injective (saturationIndex M).primeFactors
      (fun p => actualLocalModel p.val K))
    (fun k => actualTupleWeight M k * actualTupleNorm M k ^ (1 / (2 * (n : ℝ)) - 1))).trans
  exact actual_tuple_weight_moment M hn hn0 ε hε

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val _root_.infinitePlace_mult_smul
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


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors


theorem primaryIdeal_reciprocal_tail_oai {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (Q : ℝ) (hQ : 0 < Q) (hqQ : (saturationIndex M : ℝ) ≤ Q) :
    let s : ℝ := 1 / (2 * (n : ℝ))
    let hε : 0 < s / 16 := by dsimp [s] <;> positivity
    (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
      then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞)
      else 0) ≤
        (saturationIndex M : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (localProductConstant n (s / 16) hε) *
          ENNReal.ofReal Q ^ (-s / 16) := by
  dsimp only
  let s : ℝ := 1 / (2 * (n : ℝ))
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hε : 0 < s / 16 := by positivity
  apply reciprocal_norm_tail_of_moment
    (fun I : primaryIntegralIdeals K (saturationIndex M).primeFactors =>
      globalIdealWeight M (nonzeroIntegralIdealUnit I.1))
    (fun I => (Ideal.absNorm I.1.1 : ℝ≥0∞))
    (fun I => by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2))
    (fun _ => ENNReal.natCast_ne_top _) (saturationIndex M : ℝ≥0∞)
    (ENNReal.ofReal Q) (ENNReal.ofReal (localProductConstant n (s/16) hε))
    (by simpa using hQ) ENNReal.ofReal_ne_top
    (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hqQ) s hs
  have H := primaryIdeal_moment_le M hn hn0 (s/16) hε
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rw [ENNReal.ofReal_mul (localProductConstant_pos n (s / 16) hε).le,
    ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) hε.le,
    ENNReal.ofReal_natCast]
  exact mul_assoc _ _ _

end PrimeDegreePackets


end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail_oai.{u_1} := @OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail_oai.{u_1}
