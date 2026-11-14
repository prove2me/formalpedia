-- Prove2me | solution 1 for OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:14.578566+00:00
-- url     : https://prove2.me/submissions/07d15389-82a9-445e-9b6d-1fe483400b6e

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_globalContainment_eq_relativeIdealWeight

section
-- module Solutions.OAIQ244_DUKE.Compat
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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



theorem finite_completedModule_interval
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    {N : Submodule (PadicInt p) (LocalAlgebra p K) |
      N ≤ completedLattice p M ∧ ∀ x ∈ completedLattice p M,
        (p : PadicInt p)^k • x ∈ N}.Finite := by
  classical
  let f : Submodule (PadicInt p) (LocalAlgebra p K) →
      AddSubgroup (Fin n → ZMod (p^k)) := fun N =>
    (N.comap (completedLattice p M).subtype).toAddSubgroup.map (completedReduction M hn p k)
  apply Set.Finite.of_finite_image (Set.toFinite (f '' _))
  intro L hL N hN he
  have hmem (P : Submodule (PadicInt p) (LocalAlgebra p K))
      (hP : ∀ x ∈ completedLattice p M, (p : PadicInt p)^k • x ∈ P)
      (x : completedLattice p M) :
      completedReduction M hn p k x ∈ f P ↔ (x : LocalAlgebra p K) ∈ P :=
    completedReduction_mem_image_iff M hn p k (P.comap (completedLattice p M).subtype)
      (fun y => hP y y.property) x
  ext x
  by_cases hx : x ∈ completedLattice p M
  · rw [← hmem L hL.2 ⟨x,hx⟩,← hmem N hN.2 ⟨x,hx⟩,he]
  · exact iff_of_false (fun h => hx (hL.1 h)) (fun h => hx (hN.1 h))

 
theorem localModuleChoices_finite
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime] :
    (localModuleChoices M I p).Finite := by
  apply (finite_completedModule_interval (fractionalIdealFullLattice hn I) hn p
    ((saturationIndex M).factorization p)).subset
  intro N hN
  exact ⟨localModuleChoices_le M I p hN,
    fun x hx => localModuleChoices_primePower_mem M hn I p hN hx⟩

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

 

theorem saturationIndex_eq_of_locallyHomothetic
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M N : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (hMN : LocallyHomothetic M N) : saturationIndex N = saturationIndex M := by
  have h (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩;
      ∃ c : (LocalAlgebra p K)ˣ,
        completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M ∧
        completedFractionalIdeal p (saturationFractionalIdeal N) =
          (c : LocalAlgebra p K) • completedFractionalIdeal p (saturationFractionalIdeal M) := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨c,hc⟩ := hMN p hp
    have hc' : completedLattice p N = (c : LocalAlgebra p K) • completedLattice p M :=
      SetLike.coe_injective hc
    exact ⟨c,hc',local_saturation_homothety M N p c hc'⟩
  have hpow (p : labelPrimes M) (x : LocalAlgebra p.val K)
      (hx : x ∈ completedFractionalIdeal p.val (saturationFractionalIdeal N)) :
      (p.val : PadicInt p.val)^((saturationIndex M).factorization p.val) • x ∈
        completedLattice p.val N := by
    obtain ⟨c,hc,hs⟩ := h p.val Fact.out
    rw [hs] at hx
    obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [hc,smul_comm]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨_,saturation_completed_primePower_mem M hn p.val hy,rfl⟩
  have hoff (p : ℕ) (hp : p.Prime) : letI : Fact p.Prime := ⟨hp⟩;
      p ∉ Set.range (fun r : labelPrimes M => r.val) →
        completedLattice p N = completedFractionalIdeal p (saturationFractionalIdeal N) := by
    let : Fact p.Prime := ⟨hp⟩
    intro hnot
    obtain ⟨c,hc,hs⟩ := h p hp
    rw [hc,hs]
    congr 1
    apply saturation_completed_eq_off M hn p
    intro hd
    exact hnot ⟨⟨p,Nat.mem_primeFactors.mpr ⟨hp,hd,saturationIndex_ne_zero M⟩⟩,rfl⟩
  have hprod := fullLattice_relIndex_eq_prod_local
    (fractionalIdealFullLattice hn (saturationIdealUnit N)) N hn
    (fun p : labelPrimes M => p.val) Subtype.val_injective
    (fun p => (saturationIndex M).factorization p.val) hpow hoff
  change saturationIndex N = _ at hprod
  apply hprod.trans
  apply Eq.trans _ (saturationIndex_eq_prod_local M hn).symm
  apply Finset.prod_congr rfl
  intro p _
  obtain ⟨c,hc,hs⟩ := h p.val Fact.out
  change (completedLattice p.val N).toAddSubgroup.relIndex
    (completedFractionalIdeal p.val (saturationFractionalIdeal N)).toAddSubgroup = _
  rw [hc,hs]
  exact local_relIndex_smul p.val c _ _

 
theorem globalLabel_relIndex
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I) :
    N.val.toAddSubgroup.relIndex
      ((I : Submodule (𝓞 K) K).restrictScalars ℤ).toAddSubgroup = saturationIndex M := by
  have hc : saturation (globalLabelLattice M I N) =
      (I : Submodule (𝓞 K) K).restrictScalars ℤ :=
    congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K).restrictScalars ℤ)
      (globalLabelLattice_spec M I N).2.2
  rw [← (globalLabelLattice_spec M I N).1,← hc]
  exact saturationIndex_eq_of_locallyHomothetic M (globalLabelLattice M I N) hn
    (globalLabelLattice_spec M I N).2.1



theorem globalLabels_card_prod
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Nat.card (globalLabels M I) = ∏ p : labelPrimes M, Nat.card (localModuleChoices M I p.val) := by
  rw [Nat.card_congr (globalLabelEquiv M hn I),Nat.card_pi]

theorem globalLabels_card_pos
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : 0 < Nat.card (globalLabels M I) := by
  classical
  rw [globalLabels_card_prod M hn I]
  apply Finset.prod_pos
  intro p _
  let : Finite (localModuleChoices M I p.val) := (localModuleChoices_finite M hn I p.val).to_subtype
  let : Nonempty (localModuleChoices M I p.val) := (localModuleChoices_nonempty M I p.val).to_subtype
  exact Nat.card_pos



open Topology
open scoped Pointwise

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


open MeasureTheory
open scoped ENNReal

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationPreservesVolume _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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



open scoped Pointwise



open FractionalIdeal



lemma orderedUnitLog_ker
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) :
    (orderedUnitLog σ).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  rw [← NumberField.Units.dirichletUnitTheorem.logEmbedding_ker]
  ext u
  change orderedLogCoordinatesEquiv σ (NumberField.Units.logEmbedding K u) = 0 ↔ _
  exact EmbeddingLike.map_eq_zero_iff



lemma pointLattice_latticePoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice n K) (σ : OrderedEmbeddings n K)
    (hn : Module.finrank ℚ K = n) (hodd : Odd n) :
    pointLattice (latticePoint N σ) = normalizedLattice N σ := by
  have H := exists_SL_normalizedLattice N σ hn hodd
  unfold latticePoint
  rw [dite_eq_left H,pointLattice_mk]
  exact H.choose_spec

lemma tsum_nonzero_submodule_map {R V W : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid W] [Module R W] (S : Submodule R V)
    (F : V →ₗ[R] W) (hF : Function.Injective F) (f : W → ℝ≥0∞) :
    ∑' w : {w : S.map F // (w : W) ≠ 0}, f w.1.1 =
      ∑' v : {v : S // (v : V) ≠ 0}, f (F v.1.1) :=
  ((nonzeroSubmoduleMapEquiv S F hF).tsum_eq (fun w => f w.1.1)).symm

lemma scaledRealEmbedding_injective {n : ℕ} {K : Type*} [Field K]
    (σ : OrderedEmbeddings n K) (hn : 0 < n) (c : ℝ) (hc : c ≠ 0)
    (t : Fin n → ℝ) (ht : ∀ i, t i ≠ 0) :
    Function.Injective ((diagonalLinear n (fun i => c*t i)).comp (realEmbeddingMap σ)) := by
  intro a b h
  apply realEmbeddingMap_injective σ hn
  ext i
  exact mul_left_cancel₀ (mul_ne_zero hc (ht i)) (congrFun h i)



lemma embeddingMatrix_inclusion {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K) (h : N.carrier ≤ P.carrier) :
    embeddingMatrix N σ = (fullLatticeInclusionMatrix N P h).map (Int.castRingHom ℝ) *
      embeddingMatrix P σ := by
  ext i j
  have HH := congrArg (fun x : P.carrier => (x : K))
    (P.basis.sum_repr ⟨N.basis i,h (N.basis i).property⟩)
  simp only [Submodule.coe_sum,Submodule.coe_smul] at HH
  have H := congrArg (σ j) HH
  simp only [map_sum,zsmul_eq_mul,map_mul,map_intCast] at H
  exact H.symm

lemma fullLattice_relIndex_eq_natAbs_det {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (h : N.carrier ≤ P.carrier) :
    N.carrier.toAddSubgroup.relIndex P.carrier.toAddSubgroup =
      (fullLatticeInclusionMatrix N P h).det.natAbs := by
  have H := AddSubgroup.relIndex_eq_natAbs_det N.carrier.toAddSubgroup
    P.carrier.toAddSubgroup h N.basis P.basis
  have he : P.basis.toMatrix (fun i => ⟨N.basis i,h (N.basis i).property⟩) =
      (fullLatticeInclusionMatrix N P h).transpose := by
    ext i j
    rfl
  have hd : P.basis.det (fun i => ⟨N.basis i,h (N.basis i).property⟩) =
      (fullLatticeInclusionMatrix N P h).det := by
    change (P.basis.toMatrix _).det = _
    rw [he,Matrix.det_transpose]
  exact H.trans (congrArg Int.natAbs hd)

 

theorem embeddingMatrix_abs_det_index {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (N P : FullLattice n K) (σ : OrderedEmbeddings n K) (h : N.carrier ≤ P.carrier) :
    |(embeddingMatrix N σ).det| =
      (N.carrier.toAddSubgroup.relIndex P.carrier.toAddSubgroup : ℝ) *
        |(embeddingMatrix P σ).det| := by
  rw [embeddingMatrix_inclusion N P σ h,Matrix.det_mul,abs_mul,
    fullLattice_relIndex_eq_natAbs_det N P h]
  congr 1
  change |((fullLatticeInclusionMatrix N P h).map fun x : ℤ => (x : ℝ)).det| = _
  rw [← Int.cast_det]
  simp only [Nat.cast_natAbs,Int.cast_abs]



lemma tsum_nonzero_submodule_inclusion {R V : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] (N P : Submodule R V) (h : N ≤ P) (f : V → ℝ≥0∞) :
    ∑' a : {a : N // (a : V) ≠ 0}, f a.1.1 =
      ∑' a : {a : P // (a : V) ≠ 0}, if (a.1 : V) ∈ N then f a.1.1 else 0 := by
  change _ = ∑' a : {a : P // (a : V) ≠ 0},
    Set.indicator {a | (a.1 : V) ∈ N} (fun a => f a.1.1) a
  rw [← _root_.tsum_subtype]
  exact (nonzeroSubmoduleInclusionEquiv N P h).tsum_eq (fun a => f a.1.1.1)

 

theorem sum_nonzero_submodules {R V ι : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] [Fintype ι] (N : ι → Submodule R V) (P : Submodule R V)
    (h : ∀ i, N i ≤ P) (f : V → ℝ≥0∞) :
    ∑ i, ∑' a : {a : N i // (a : V) ≠ 0}, f a.1.1 =
      ∑' a : {a : P // (a : V) ≠ 0},
        (Nat.card {i : ι // (a.1 : V) ∈ N i} : ℝ≥0∞) * f a.1.1 := by
  simp_rw [tsum_nonzero_submodule_inclusion _ P (h _) f]
  rw [← tsum_fintype (L := SummationFilter.unconditional ι),ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_fintype]
  simp only [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]



lemma logFlowWeights_pos {d : ℕ} (u : LogCoordinates d) (i : Fin (d+1)) :
    0 < logFlowWeights u i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [logFlowWeights,Real.exp_pos]

lemma pointLattice_rightAction_signs {n : ℕ} (x : X n) (hn : Odd n)
    (w : Fin n → SignTypeˣ) :
    pointLattice (rightAction x (positiveSignMatrix hn w)) =
      (pointLattice x).map (diagonalLinear n (fun i => signValue (w i))) := by
  induction x using Quotient.inductionOn with
  | h g => exact rowLattice_positiveSignMatrix g.1 hn w

lemma pointLattice_signed_flow {d : ℕ} (x : X (d+1)) (hn : Odd (d+1))
    (w : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) :
    pointLattice (orbitMap (rightAction x (positiveSignMatrix hn w)) u) =
      (pointLattice x).map (diagonalLinear (d+1) (fun i => signValue (w i)*logFlowWeights u i)) := by
  unfold orbitMap
  rw [pointLattice_rightAction_diagonal _ (diagonalFlow u) (logFlowWeights u) rfl,
    pointLattice_rightAction_signs,← Submodule.map_comp]
  congr 1
  ext a i
  simp [diagonalLinear,mul_left_comm,mul_assoc]

lemma signValue_ne_zero (w : SignTypeˣ) : signValue w ≠ 0 := by
  rcases signValue_eq_one_or_neg_one w with h | h <;> simp [h]

 

theorem siegelTransform_latticePoint_signed_flow {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (N : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (w : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    siegelTransform f (orbitMap (rightAction (latticePoint N σ) (positiveSignMatrix hodd w)) u) =
      ∑' a : {a : N.carrier // (a : K) ≠ 0},
        f (fun i => |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/(d+1:ℕ)) *
          (signValue (w i)*logFlowWeights u i) * σ i a.1.1) := by
  let c := |(embeddingMatrix N σ).det| ^ (-(1:ℝ)/(d+1:ℕ))
  have hc : c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos
    (abs_pos.mpr (embeddingMatrix_det_ne_zero N σ hn)) _)
  have he : (diagonalLinear (d+1) (fun i => signValue (w i)*logFlowWeights u i)).comp
      (diagonalLinear (d+1) (fun _ => c)) =
      diagonalLinear (d+1) (fun i => c*(signValue (w i)*logFlowWeights u i)) := by
    ext a i
    simp [diagonalLinear,mul_left_comm,mul_assoc]
  unfold siegelTransform
  rw [pointLattice_signed_flow,pointLattice_latticePoint N σ hn hodd,
    normalizedLattice_as_map,← Submodule.map_comp,he,← Submodule.map_comp]
  exact tsum_nonzero_submodule_map N.carrier _
    (scaledRealEmbedding_injective σ (by omega) c hc _
      (fun i => mul_ne_zero (signValue_ne_zero _) (logFlowWeights_pos u i).ne')) f

lemma globalLabel_le_ideal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I) :
    N.val ≤ (I : Submodule (𝓞 K) K).restrictScalars ℤ := by
  rw [← (globalLabelLattice_spec M I N).1]
  convert le_saturation (globalLabelLattice M I N) using 1
  all_goals try with_reducible_and_instances rfl
  exact congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => (J : Submodule (𝓞 K) K).restrictScalars ℤ)
    (globalLabelLattice_spec M I N).2.2.symm

 

theorem globalLabel_abs_det {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : globalLabels M I) :
    |(embeddingMatrix (globalLabelLattice M I N) σ).det| =
      (saturationIndex M : ℝ) * |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det| := by
  have hi : (globalLabelLattice M I N).carrier ≤ (fractionalIdealFullLattice hn I).carrier := by
    rw [(globalLabelLattice_spec M I N).1]
    exact globalLabel_le_ideal M I N
  rw [embeddingMatrix_abs_det_index _ _ σ hi]
  congr 1
  change ((globalLabelLattice M I N).carrier.toAddSubgroup.relIndex
    ((I : Submodule (𝓞 K) K).restrictScalars ℤ).toAddSubgroup : ℝ) = _
  rw [(globalLabelLattice_spec M I N).1,globalLabel_relIndex M hn I N]



theorem globalLabel_siegelTransform_average {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) [Fintype (globalLabels M I)]
    (w : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    (Nat.card (globalLabels M I) : ℝ≥0∞)⁻¹ *
      ∑ N : globalLabels M I, siegelTransform f
        (orbitMap (signedGlobalLabelPoint M σ hodd I ⟨N,w⟩) u) =
      ∑' a : nonzeroIdealElements I, globalIdealWeight M (relativeElementIdeal I a.1) *
        f (fun i => ((saturationIndex M : ℝ) *
          |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ)) *
          (signValue (w i)*logFlowWeights u i) * σ i a.1.1) := by
  let c := ((saturationIndex M : ℝ) *
    |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ))
  let F : K → ℝ≥0∞ := fun a => f (fun i => c * (signValue (w i)*logFlowWeights u i) * σ i a)
  have he (N : globalLabels M I) : siegelTransform f
        (orbitMap (signedGlobalLabelPoint M σ hodd I ⟨N,w⟩) u) =
      ∑' a : {a : N.val // (a : K) ≠ 0}, F a.1.1 := by
    unfold signedGlobalLabelPoint
    rw [siegelTransform_latticePoint_signed_flow _ σ hn hodd w u f,globalLabel_abs_det M σ hn I N]
    change (∑' a : {a : (globalLabelLattice M I N).carrier // (a : K) ≠ 0}, F a.1.1) = _
    rw [(globalLabelLattice_spec M I N).1]
  simp_rw [he]
  rw [sum_nonzero_submodules _ ((I : Submodule (𝓞 K) K).restrictScalars ℤ)
    (globalLabel_le_ideal M I) F,← ENNReal.tsum_mul_left]
  rw [← (nonzeroIdealElementEquiv I).tsum_eq]
  apply tsum_congr
  intro a
  rw [← mul_assoc,mul_comm ((Nat.card (globalLabels M I) : ℝ≥0∞)⁻¹),← div_eq_mul_inv]
  change _ * F a.1.1 = globalIdealWeight M (relativeElementIdeal I (Units.mk0 a.1.1 a.2)) * F a.1.1
  congr 1
  exact globalContainment_eq_relativeIdealWeight M hn I (Units.mk0 a.1.1 a.2) a.1.2

 

theorem tsum_comp_surjective_addHom {A B : Type*} [AddGroup A] [AddGroup B]
    (additiveMap : A →+ B) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    (f : B → ℝ≥0∞) :
    (∑' a, f (additiveMap a)) = (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' b, f b := by
  rw [← ENNReal.tsum_fiberwise (fun a => f (additiveMap a)) additiveMap,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  let e := AddMonoidHom.fiberEquivKerOfSurjective hφ b
  let := Fintype.ofFinite additiveMap.ker
  let := Fintype.ofEquiv additiveMap.ker e.symm
  calc
    (∑' a : additiveMap ⁻¹' {b}, f (additiveMap a)) = ∑' _a : additiveMap ⁻¹' {b}, f b := by
      apply tsum_congr
      intro a
      rw [show additiveMap a = b from a.property]
    _ = (Nat.card additiveMap.ker : ℝ≥0∞) * f b := by
      rw [tsum_fintype,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,
        ← Nat.card_eq_fintype_card,Nat.card_congr e]

 

theorem lintegral_tsum_addHom_fundamentalDomain {d : ℕ} {A : Type*} [AddGroup A]
    (L : Submodule ℤ (Fin d → ℝ)) [Countable L]
    (additiveMap : A →+ L) (hφ : Function.Surjective additiveMap) [Finite additiveMap.ker]
    {t : Set (Fin d → ℝ)} (ht : IsAddFundamentalDomain L t volume)
    (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑' a, f ((additiveMap a : Fin d → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∫⁻ v, f v := by
  have he (u : Fin d → ℝ) : (∑' a, f ((additiveMap a : Fin d → ℝ)+u)) =
      (Nat.card additiveMap.ker : ℝ≥0∞) * ∑' p : L, f ((p : Fin d → ℝ)+u) :=
    tsum_comp_surjective_addHom additiveMap hφ (fun p => f ((p : Fin d → ℝ)+u))
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [ht.lintegral_eq_tsum'' f]
  exact lintegral_tsum (fun p => (hf.comp (measurable_const.add measurable_id)).aemeasurable)



lemma logFlowWeights_add {d : ℕ} (u t : LogCoordinates d) :
    logFlowWeights (u+t) = logFlowWeights u * logFlowWeights t := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [logFlowWeights,Real.exp_add,Finset.sum_add_distrib,mul_comm]

lemma continuous_logFlowWeights {d : ℕ} : Continuous (@logFlowWeights d) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [logFlowWeights,Fin.snoc_last,Fin.snoc_castSucc]
  · fun_prop
  · fun_prop

lemma measurable_signedFlowSum {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (v : Fin (d+1) → ℝ) : Measurable (signedFlowSum f v) := by
  unfold signedFlowSum
  apply Finset.measurable_sum
  intro w _
  exact hf.comp (Measurable.of_eval (fun i =>
    (((measurable_pi_apply i).comp continuous_logFlowWeights.measurable).const_mul _).mul_const _))

lemma signedFlowSum_sign_log_translate {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (v : Fin (d+1) → ℝ) (s : Fin (d+1) → SignTypeˣ) (p u : LogCoordinates d) :
    signedFlowSum f (fun i => signValue (s i)*logFlowWeights p i*v i) u =
      signedFlowSum f v (p+u) := by
  have he := Equiv.sum_comp (Equiv.mulLeft s)
    (fun w : Fin (d+1) → SignTypeˣ => f (fun i => signValue (w i)*logFlowWeights (p+u) i*v i))
  unfold signedFlowSum
  rw [← he]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  ext i
  simp only [Equiv.coe_mulLeft,Pi.mul_apply,map_mul,logFlowWeights_add]
  ring

lemma logFlowWeights_orderedUnitLog {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) (z : (𝓞 K)ˣ) :
    logFlowWeights (orderedUnitLog σ (Additive.ofMul z)) = fun i => |σ i (z : K)| := by
  have h := diagonalFlow_abs_orderedUnitLog σ z
  have H (i : Fin (d+1)) := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ => A i i) h
  funext i
  exact by simpa only [diagonalFlow,logFlowWeights,Matrix.diagonal_apply_eq] using H i

 

lemma signedFlowSum_mul_unit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (c : ℝ) (a : K) (z : (𝓞 K)ˣ) (u : LogCoordinates d) :
    signedFlowSum f (fun i => c*σ i ((z : K)*a)) u =
      signedFlowSum f (fun i => c*σ i a) (orderedUnitLog σ (Additive.ofMul z)+u) := by
  rw [← signedFlowSum_sign_log_translate f (fun i => c*σ i a) (unitSigns σ z)]
  congr 1
  ext i
  rw [logFlowWeights_orderedUnitLog,signValue_unitSigns,map_mul]
  ring



lemma orderedUnitLogOnto_surjective {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    Function.Surjective (orderedUnitLogOnto σ) := by
  intro p
  obtain ⟨u,_,hu⟩ := (mem_orderedLogSubgroup σ ⊤ p.val).mp p.property
  exact ⟨Additive.ofMul u,Subtype.ext hu⟩

lemma orderedUnitLogOnto_ker {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    (orderedUnitLogOnto σ).ker = (NumberField.Units.torsion K).toAddSubgroup := by
  rw [orderedUnitLogOnto,AddMonoidHom.ker_codRestrict,orderedUnitLog_ker]

lemma orderedUnitLogOnto_ker_card {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hodd : Odd (Module.finrank ℚ K)) : Nat.card (orderedUnitLogOnto σ).ker = 2 := by
  rw [orderedUnitLogOnto_ker]
  let e : (NumberField.Units.torsion K).toAddSubgroup ≃ NumberField.Units.torsion K :=
    ⟨(fun u => ⟨u.val.toMul,u.property⟩),(fun u => ⟨Additive.ofMul u.val,u.property⟩),
      (fun _ => rfl),(fun _ => rfl)⟩
  rw [Nat.card_congr e]
  exact NumberField.Units.torsionOrder_eq_two_of_odd_finrank hodd

 

theorem lintegral_signedFlowSum_unit {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hodd : Odd (Module.finrank ℚ K))
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) (c : ℝ) (a : K) :
    (∫⁻ u in t, ∑' z : (𝓞 K)ˣ, signedFlowSum f (fun i => c*σ i ((z : K)*a)) u) =
      2 * ∫⁻ u, signedFlowSum f (fun i => c*σ i a) u := by
  simp_rw [signedFlowSum_mul_unit σ f c a]
  let unitLog := orderedUnitLogOnto σ
  let : Finite unitLog.ker := Nat.finite_of_card_ne_zero (by rw [orderedUnitLogOnto_ker_card σ hodd]; decide)
  have he := lintegral_tsum_addHom_fundamentalDomain (orderedLogSubgroup σ ⊤) unitLog
    (orderedUnitLogOnto_surjective σ) ht (signedFlowSum f (fun i => c*σ i a))
    (measurable_signedFlowSum hf _)
  rw [orderedUnitLogOnto_ker_card σ hodd] at he
  exact he



lemma lintegral_signedFlowSum_productFiberVector {d : ℕ}
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) (z : ℝ) :
    (∫⁻ u, signedFlowSum f (productFiberVector z) u) = productFiberIntegral f z := by
  unfold signedFlowSum productFiberIntegral
  rw [lintegral_finsetSum _ (by
    intro w _
    exact hf.comp (Measurable.of_eval (fun i =>
      (((measurable_pi_apply i).comp continuous_logFlowWeights.measurable).const_mul _).mul_const _)))]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  funext u
  congr 1
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [productFiberVector,logFlowWeights,mul_comm,mul_left_comm]

 

theorem lintegral_signedFlowSum_eq_productFiberIntegral {d : ℕ}
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (v : Fin (d+1) → ℝ) (hv : ∀ i, v i ≠ 0) :
    (∫⁻ u, signedFlowSum f v u) = productFiberIntegral f (∏ i, |v i|) := by
  let p : LogCoordinates d := fun i => Real.log |v i.castSucc|
  let s : Fin (d+1) → SignTypeˣ := fun i =>
    Units.map (signHom : ℝ →*₀ SignType).toMonoidHom (Units.mk0 (v i) (hv i))
  have hs (i : Fin (d+1)) : signValue (s i) * |v i| = v i := sign_mul_abs _
  have hp : logFlowWeights p (Fin.last d) = (∏ i : Fin d, |v i.castSucc|)⁻¹ := by
    simp only [logFlowWeights,Fin.snoc_last,Real.exp_neg,Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact Real.exp_log (abs_pos.mpr (hv _))
  have hp0 : (∏ i : Fin d, |v i.castSucc|) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => abs_ne_zero.mpr (hv _))
  have he : v = fun i => signValue (s i)*logFlowWeights p i*productFiberVector (∏ j, |v j|) i := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [productFiberVector,Fin.snoc_last,hp,Fin.prod_univ_castSucc]
      rw [mul_assoc,inv_mul_cancel_left₀ hp0,hs]
    · simp only [productFiberVector,Fin.snoc_castSucc,logFlowWeights,p,mul_one]
      rw [Real.exp_log (abs_pos.mpr (hv _)),hs]
  conv_lhs => rw [he]
  simp_rw [signedFlowSum_sign_log_translate]
  rw [lintegral_add_left_eq_self,lintegral_signedFlowSum_productFiberVector f hf]

 

lemma tsum_relativeElementIdeal {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (W : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞) (F : K → ℝ≥0∞) :
    (∑' a : nonzeroIdealElements I, W (relativeElementIdeal I a.1) * F a.1.1) =
      ∑' J : integralIdealClassFiber I, W J.1 *
        ∑' z : (𝓞 K)ˣ, F ((z : K)*(idealElementRepresentative I J).1.1) := by
  rw [← (idealElementDecomposition I).tsum_eq,ENNReal.tsum_sigma']
  apply tsum_congr
  intro J
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  have h := congrArg Subtype.val ((relativeElementClassMap_unitAction I z
    (idealElementRepresentative I J)).trans (idealElementRepresentative_spec I J))
  change W (relativeElementIdeal I (idealElementUnitAction I z (idealElementRepresentative I J)).1) *
    F ((z : K)*(idealElementRepresentative I J).1.1) = _
  rw [show relativeElementIdeal I (idealElementUnitAction I z (idealElementRepresentative I J)).1 = J.1 from h]

 

theorem lintegral_weighted_idealElements {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hodd : Odd (Module.finrank ℚ K))
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (W : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ u in t, ∑' a : nonzeroIdealElements I,
      W (relativeElementIdeal I a.1)*signedFlowSum f (fun i => c*σ i a.1.1) u) =
      2 * ∑' J : integralIdealClassFiber I, W J.1 *
        productFiberIntegral f (∏ i, |c*σ i (idealElementRepresentative I J).1.1|) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable (𝓞 K) := RingOfIntegers.coe_injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (𝓞 K)ˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : Countable (integralIdealClassFiber I) := (relativeElementClassMap_surjective I).countable
  have he (u : LogCoordinates d) := tsum_relativeElementIdeal I W
    (fun a => signedFlowSum f (fun i => c*σ i a) u)
  simp_rw [he]
  rw [lintegral_tsum (fun J => ((Measurable.tsum (fun z : (𝓞 K)ˣ =>
    measurable_signedFlowSum hf (fun i => c*σ i ((z : K)*(idealElementRepresentative I J).1.1)))).const_mul _).aemeasurable)]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro J
  rw [lintegral_const_mul _ (Measurable.tsum (fun z : (𝓞 K)ˣ => measurable_signedFlowSum hf _)),
    lintegral_signedFlowSum_unit σ hodd ht f hf c,
    lintegral_signedFlowSum_eq_productFiberIntegral f hf _ (fun i =>
      mul_ne_zero hc (by simpa only [_root_.map_zero] using (σ i).injective.ne (idealElementRepresentative I J).1.ne_zero))]
  ring

lemma integralEmbeddingMatrix_det_sq {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (b : Basis (Fin n) ℤ (𝓞 K)) :
    (Matrix.det (fun i j => σ j (b i)))^2 = (NumberField.discr K : ℝ) := by
  let bQ := b.localizationLocalization ℚ ℤ⁰ K
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (b i)
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ bQ (orderedComplexEmbeddings σ hn)
  have hm : Algebra.embeddingsMatrixReindex ℚ ℂ bQ (orderedComplexEmbeddings σ hn) =
      B.map Complex.ofRealHom := by
    ext i j
    change Complex.ofReal (σ j (bQ i)) = Complex.ofReal (σ j (b i))
    rw [show bQ i = (algebraMap (𝓞 K) K) (b i) from b.localizationLocalization_apply ℚ ℤ⁰ K i]
  rw [hm,show (B.map Complex.ofRealHom).det = Complex.ofRealHom B.det from
    (Complex.ofRealHom.map_det B).symm] at h
  have hd : Algebra.discr ℚ bQ = (NumberField.discr K : ℚ) := by
    dsimp only [bQ]
    rw [Algebra.discr_localizationLocalization,NumberField.discr_eq_discr]
    rfl
  rw [hd] at h
  apply Complex.ofReal_injective
  simpa only [B,map_intCast,Complex.ofRealHom_eq_coe,Complex.ofReal_intCast,Complex.ofReal_pow] using h.symm

lemma embeddingMatrix_det_basisChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (σ : OrderedEmbeddings n K)
    (b : Basis (Fin n) ℚ K) :
    (embeddingMatrix M σ).det = (b.det (fun i => (M.basis i : K)) : ℝ)*
      Matrix.det (fun i j => σ j (b i)) := by
  let C := b.toMatrix (fun i => (M.basis i : K))
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j => σ j (b i)
  have hm : embeddingMatrix M σ = C.transpose.map (algebraMap ℚ ℝ) * B := by
    ext i j
    have h := congrArg (σ j) (b.sum_repr (M.basis i : K))
    simp only [Algebra.smul_def,map_sum,map_mul,RingHom.map_rat_algebraMap] at h
    exact h.symm
  rw [hm,Matrix.det_mul,show (C.transpose.map (algebraMap ℚ ℝ)).det =
    algebraMap ℚ ℝ C.transpose.det from ((algebraMap ℚ ℝ).map_det C.transpose).symm,
    Matrix.det_transpose]
  rfl

 

theorem embeddingMatrix_abs_det_fractionalIdeal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det| =
      Real.sqrt |(NumberField.discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  let b : Basis (Fin n) ℤ (𝓞 K) := (Module.Free.chooseBasis ℤ (𝓞 K)).reindex
    (Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ (𝓞 K)),RingOfIntegers.rank,hn]))
  rw [embeddingMatrix_det_basisChange _ σ (b.localizationLocalization ℚ ℤ⁰ K),abs_mul]
  have hnrm := FractionalIdeal.abs_det_basis_change b (I : FractionalIdeal (𝓞 K)⁰ K)
    (fractionalIdealFullLattice hn I).basis
  have hnrm' : |((b.localizationLocalization ℚ ℤ⁰ K).det
      (fun i => ((fractionalIdealFullLattice hn I).basis i : K)) : ℝ)| =
        (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    exact_mod_cast hnrm
  rw [hnrm']
  have hdet : |Matrix.det (fun i j => σ j ((b.localizationLocalization ℚ ℤ⁰ K) i))| =
      Real.sqrt |(NumberField.discr K : ℝ)| := by
    simp only [Basis.localizationLocalization_apply]
    conv_rhs => rw [← integralEmbeddingMatrix_det_sq σ hn b,abs_of_nonneg (sq_nonneg _),Real.sqrt_sq_eq_abs]
  rw [hdet,mul_comm]

lemma prod_orderedEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∏ i, σ i a = (Algebra.norm ℚ a : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  rw [← (orderedComplexEmbeddings σ hn).prod_comp] at h
  change (algebraMap ℚ ℂ) (Algebra.norm ℚ a) = ∏ i, Complex.ofReal (σ i a) at h
  rw [← Complex.ofReal_prod] at h
  change (Algebra.norm ℚ a : ℂ) = _ at h
  simpa only [Complex.ofReal_ratCast] using h.symm

lemma prod_abs_orderedEmbeddings {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (a : K) :
    ∏ i, |σ i a| = |(Algebra.norm ℚ a : ℝ)| := by
  rw [← Finset.abs_prod,prod_orderedEmbeddings σ hn]

lemma fractionalIdeal_absNorm_pos {K : Type*} [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I.1)
    (fun h => I.ne_zero (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))

lemma normalization_rpow_pow {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    (x^(-(1:ℝ)/(n:ℝ)))^n = x⁻¹ := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ hn',Real.rpow_neg_one]

lemma normalized_ideal_coordinate_product {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (σ : OrderedEmbeddings n K) (hn : Module.finrank ℚ K = n) (hnpos : 0 < n)
    {q : ℝ} (hq : 0 < q) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : K) :
    (∏ i, |(q*|(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|)^(-(1:ℝ)/n)*σ i a|) =
      (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ a *
        (I⁻¹).val) : ℝ)/(q*Real.sqrt |(NumberField.discr K : ℝ)|) := by
  have hD : 0 < Real.sqrt |(NumberField.discr K : ℝ)| := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hI := fractionalIdeal_absNorm_pos I
  rw [embeddingMatrix_abs_det_fractionalIdeal σ hn I]
  simp_rw [abs_mul,Finset.prod_mul_distrib]
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,abs_of_pos (Real.rpow_pos_of_pos (mul_pos hq (mul_pos hD hI)) _),
    normalization_rpow_pow hnpos (mul_pos hq (mul_pos hD hI)),prod_abs_orderedEmbeddings σ hn]
  have hinv : FractionalIdeal.absNorm (I⁻¹).val =
      (FractionalIdeal.absNorm I.1)⁻¹ := by
    have h := congrArg (fun J : FractionalIdeal (𝓞 K)⁰ K => FractionalIdeal.absNorm J) (Units.mul_inv I)
    rw [map_mul,map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [map_mul,FractionalIdeal.absNorm_span_singleton,hinv,Rat.cast_mul,Rat.cast_inv,Rat.cast_abs]
  ring

lemma sum_signedGlobalLabel {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    (F : SignedGlobalLabel M I → ℝ≥0∞) :
    (∑ x : SignedGlobalLabel M I, F x) =
      ∑ w : Fin n → SignTypeˣ, ∑ N : globalLabels M I, F ⟨N,w⟩ := by
  let e := (signedGlobalLabelEquiv M I).trans (Equiv.prodComm _ _)
  calc
    _ = ∑ x : (Fin n → SignTypeˣ) × globalLabels M I, F ⟨x.2,x.1⟩ :=
      (e.symm.sum_comp F).symm
    _ = _ := Fintype.sum_prod_type _

 

lemma signedLabel_siegelTransform_average {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    (Nat.card (globalLabels M I) : ℝ≥0∞)⁻¹ *
      ∑ x : SignedGlobalLabel M I, siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u) =
      ∑' a : nonzeroIdealElements I, globalIdealWeight M (relativeElementIdeal I a.1) *
        signedFlowSum f (fun i => ((saturationIndex M : ℝ) *
          |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ)) * σ i a.1.1) u := by
  rw [sum_signedGlobalLabel,Finset.mul_sum]
  simp_rw [globalLabel_siegelTransform_average M σ hn hodd]
  rw [← tsum_fintype (L := SummationFilter.unconditional _),ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_fintype, signedFlowSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  congr 2
  ext i
  ring

lemma signedLabel_siegelTransform_sum {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    (u : LogCoordinates d) (f : (Fin (d+1) → ℝ) → ℝ≥0∞) :
    (∑ x : SignedGlobalLabel M I, siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u)) =
      (Nat.card (globalLabels M I) : ℝ≥0∞) *
      ∑' a : nonzeroIdealElements I, globalIdealWeight M (relativeElementIdeal I a.1) *
        signedFlowSum f (fun i => ((saturationIndex M : ℝ) *
          |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ)) * σ i a.1.1) u := by
  rw [← signedLabel_siegelTransform_average M σ hn hodd I u f]
  exact (ENNReal.mul_inv_cancel_left (by exact_mod_cast (globalLabels_card_pos M hn I).ne') (by finiteness)).symm

 

theorem signedLabel_siegelTransform_lintegral_oai {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑ x : SignedGlobalLabel M I,
      siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u)) =
      (Nat.card (globalLabels M I) : ℝ≥0∞) * (2 *
      ∑' J : integralIdealClassFiber I, globalIdealWeight M J.1 *
        productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) /
          ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|))) := by
  let : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let : Countable Kˣ := Units.val_injective.countable
  let : Countable (nonzeroIdealElements I) := by
    change Countable {a : Kˣ // (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)}
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let c := ((saturationIndex M : ℝ) *
    |(embeddingMatrix (fractionalIdealFullLattice hn I) σ).det|) ^ (-(1:ℝ)/(d+1:ℕ))
  have hq : 0 < (saturationIndex M : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M)
  have hc : c ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hq
    (abs_pos.mpr (embeddingMatrix_det_ne_zero _ σ hn))) _).ne'
  simp_rw [signedLabel_siegelTransform_sum M σ hn hodd I]
  rw [lintegral_const_mul _ (Measurable.tsum (fun a : nonzeroIdealElements I =>
    (measurable_signedFlowSum hf (fun i => c*σ i a.1.1)).const_mul _))]
  rw [lintegral_weighted_idealElements σ (hn ▸ hodd) ht I (globalIdealWeight M) f hf c hc]
  congr 2
  apply tsum_congr
  intro J
  congr 2
  rw [show (∏ i, |c*σ i (idealElementRepresentative I J).1.1|) =
      (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰
        (idealElementRepresentative I J).1.1 * (I⁻¹).val) : ℝ) /
        ((saturationIndex M : ℝ)*Real.sqrt |(NumberField.discr K : ℝ)|) from
    normalized_ideal_coordinate_product σ hn (Nat.succ_pos _) hq I _]
  have hJ := congrArg (fun J : integralIdealClassFiber I => J.1.val) (idealElementRepresentative_spec I J)
  simp only [relativeElementClassMap,relativeElementIdeal,Units.val_mul,coe_toPrincipalIdeal] at hJ
  rw [hJ]

end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral_oai.{u_1} := @OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral_oai.{u_1}
