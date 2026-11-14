-- Prove2me | solution 1 for OAI.PrimeDegreePackets.packet_tight_of_zeta_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:45.658554+00:00
-- url     : https://prove2.me/submissions/d1a227b8-5106-4970-9560-6e2ae229e628

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke014
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_packetMeasure_lintegral_signedLogAverage
import Theorems.Thm_OAI_PrimeDegreePackets_signedLabel_siegelTransform_lintegral
import Theorems.Thm_OAI_PrimeDegreePackets_weightedIdeal_realInterval_of_zeta_scale

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.model_units_measurableSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

theorem globalLabels_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (globalLabels M I).Finite := by
  let (p : labelPrimes M) : Finite (localModuleChoices M I p.val) :=
    (localModuleChoices_finite M hn I p.val).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective _ (globalLabelCompletions_injective M hn I))


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

lemma localIdealWeight_le_one {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : localIdealWeight M p J ≤ 1 :=
  prob_le_one

lemma globalIdealWeight_le_one {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : globalIdealWeight M J ≤ 1 := by
  apply Finset.prod_le_one'
  intro prime _
  exact localIdealWeight_le_one M prime.val J


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
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



lemma fieldDiscriminant_one_le (K : Type*) [Field K] [NumberField K] :
    1 ≤ |(NumberField.discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

lemma packetScale_pos {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : 0 < packetScale M := by
  unfold packetScale
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M))
    (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (fieldDiscriminant_one_le K)))



theorem latticePoint_diagonalOrbit_isCompact {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d + 1) K)
    (σ : OrderedEmbeddings (d + 1) K) (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) : IsCompact (diagonalOrbit (latticePoint M σ)) := by
  let := latticePoint_period_isZLattice M σ hn hodd
  apply IsZLattice.isCompact_range_of_periodic (periodGroup (latticePoint M σ)).toIntSubmodule
    (orbitMap (latticePoint M σ)) (continuous_orbitMap _)
  intro z w hw
  change orbitMap (latticePoint M σ) w = latticePoint M σ at hw
  rw [add_comm z w, orbitMap_add, hw]



lemma diagonalOrbit_rightAction_of_diagonal {d : ℕ} (x : X (d + 1)) (g : G (d + 1))
    (hg : ∀ i j, i ≠ j → g.1 i j = 0) :
    diagonalOrbit (rightAction x g) = (fun y => rightAction y g) '' diagonalOrbit x := by
  ext y
  simp only [diagonalOrbit, Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨orbitMap x u, ⟨u, rfl⟩, (orbitMap_rightAction_of_diagonal x g hg u).symm⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, orbitMap_rightAction_of_diagonal x g hg u⟩



theorem packetOrbit_isCompact {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {M : FullLattice (d + 1) K}
    {σ : OrderedEmbeddings (d + 1) K} (hn : Module.finrank ℚ K = d + 1)
    (hodd : Odd (d + 1)) (O : packetOrbits M σ) : IsCompact O.1 := by
  obtain ⟨M', _, w, hw, hO⟩ := O.property
  rw [hO, diagonalOrbit_rightAction_of_diagonal _ _ hw.1]
  exact (latticePoint_diagonalOrbit_isCompact M' σ hn hodd).image (continuous_rightAction w)



open scoped Pointwise



open FractionalIdeal



theorem signedGlobalLabel_finite {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Finite (SignedGlobalLabel M I) := by
  let := (globalLabels_finite M hn I).to_subtype
  exact Finite.of_injective (fun x : SignedGlobalLabel M I => (x.lattice,x.signs)) (by
    intro x y h; exact SignedGlobalLabel.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

lemma continuous_integerRowMap {n : ℕ} (z : Fin n → ℤ) :
    Continuous (fun g : G n => integerRowMap g.1 z) := by
  change Continuous (fun g : G n => ∑ i, z i • g.1 i)
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).const_smul (z i)



lemma siegelTransform_mk {n : ℕ} (f : (Fin n → ℝ) → ℝ≥0∞) (g : G n) :
    siegelTransform f (Quotient.mk _ g) =
      ∑' z : {z : Fin n → ℤ // z ≠ 0}, f (integerRowMap g.1 z.1) := by
  change (∑' v : {v : rowLattice g.1 // (v : Fin n → ℝ) ≠ 0}, f v.1.1) = _
  exact ((nonzeroIntegerRowEquiv g).tsum_eq (fun v => f v.1.1)).symm

 

lemma measurable_siegelTransform {n : ℕ} {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf : Measurable f) : Measurable (siegelTransform f) := by
  let : PolishSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (PolishSpace (Fin n → Fin n → ℝ))
  let : PolishSpace (G n) := Matrix.SpecialLinearGroup.isClosedEmbedding_val.polishSpace
  let : MeasurableSpace (G n) := borel (G n)
  let : BorelSpace (G n) := ⟨rfl⟩
  have hq : Measurable (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) :=
    continuous_quotient_mk'.measurable
  apply (hq.measurable_comp_iff_of_surjective Quotient.mk_surjective).mp
  change Measurable (fun g : G n => siegelTransform f (Quotient.mk _ g))
  simp_rw [siegelTransform_mk]
  exact Measurable.tsum (fun z => hf.comp (continuous_integerRowMap z.1).measurable)

lemma logSubgroup_top {K : Type*} [Field K] [NumberField K] :
    logSubgroup (⊤ : Subgroup (𝓞 K)ˣ) = NumberField.Units.unitLattice K := rfl



lemma orderedUnitRank {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    NumberField.Units.rank K = d := by
  rw [← NumberField.Units.finrank_eq_rank]
  rw [(orderedLogCoordinatesEquiv σ).finrank_eq]
  simp

 

theorem orderedLogSubgroup_covolume_eq_regulator {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K) :
    ZLattice.covolume (orderedLogSubgroup σ ⊤) = NumberField.Units.regulator K := by
  let ec := orderedLogCoordinatesEquiv σ
  let er : Fin (NumberField.Units.rank K) ≃ Fin d := finCongr (orderedUnitRank σ)
  let b := ((NumberField.Units.basisUnitLattice K).ofZLatticeComap ℝ
    (NumberField.Units.unitLattice K) ec.symm).reindex er
  have hb : ∀ i j, (b i : Fin d → ℝ) j =
      Real.log |σ j.castSucc (NumberField.Units.fundSystem K (er.symm i) : K)| := by
    intro i j
    simp only [b,Basis.reindex_apply,Basis.ofZLatticeComap_apply,LinearEquiv.symm_symm]
    rw [← NumberField.Units.logEmbedding_fundSystem]
    exact orderedUnitLog_apply σ _ j
  let : DiscreteTopology (ZLattice.comap ℝ (NumberField.Units.unitLattice K) ec.symm.toLinearMap) :=
    ZLattice.comap_discreteTopology ℝ _ ec.symm.toContinuousLinearEquiv.continuous ec.symm.injective
  let : IsZLattice ℝ (ZLattice.comap ℝ (NumberField.Units.unitLattice K) ec.symm.toLinearMap) :=
    instIsZLatticeComap ℝ _ ec.symm.toContinuousLinearEquiv
  change ZLattice.covolume (ZLattice.comap ℝ (logSubgroup ⊤) ec.symm.toLinearMap) = _
  rw [logSubgroup_top,ZLattice.covolume_eq_det _ b]
  let ep := orderedDeletedPlacesEquiv σ
  have hr := NumberField.Units.regulator_eq_det K (orderedRealPlaces σ (Fin.last d))
    (ep.symm.trans er.symm)
  rw [hr]
  congr 1
  let A : Matrix {w : NumberField.InfinitePlace K // w ≠ orderedRealPlaces σ (Fin.last d)}
      {w : NumberField.InfinitePlace K // w ≠ orderedRealPlaces σ (Fin.last d)} ℝ :=
    fun i w => (NumberField.InfinitePlace.mult w.val : ℝ) *
      Real.log (w.val (NumberField.Units.fundSystem K ((ep.symm.trans er.symm) i) : K))
  change (Matrix.of ((↑) ∘ b)).det = A.det
  rw [← Matrix.det_reindex_self ep.symm A]
  congr 1
  ext i j
  change (b i : Fin d → ℝ) j =
    ((ep j).val.mult : ℝ)*Real.log ((ep j).val
      (NumberField.Units.fundSystem K (er.symm (ep.symm (ep i))) : K))
  rw [hb,Equiv.symm_apply_apply,(NumberField.IsTotallyReal.isReal _).mult_eq_one]
  simp only [Nat.cast_one,one_mul,ep,orderedDeletedPlacesEquiv,Equiv.trans_apply,
    Equiv.subtypeEquiv_apply,finSuccAboveEquiv_apply,Fin.succAbove_last,orderedRealPlaces_apply]



lemma tsum_idealClassPartition (K : Type*) [Field K] [NumberField K]
    (F : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℝ≥0∞) :
    (∑' c : ClassGroup (𝓞 K), ∑' J : integralIdealClassFiber (classRepresentative K c), F J.1) =
      ∑' J : integralFractionalIdeals K, F J.1 := by
  calc
    _ = ∑' x : (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)), F x.2.1 :=
      (ENNReal.tsum_sigma' (fun x : (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (classRepresentative K c)) => F x.2.1)).symm
    _ = _ := (idealClassPartitionEquiv K).tsum_eq (fun J : integralFractionalIdeals K => F J.val)



lemma packetUnfoldingCoefficient {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hn : Module.finrank ℚ K = n) (hodd : Odd n) :
    2 / ((NumberField.classNumber K : ℝ) * 2^n * NumberField.Units.regulator K) =
      1 / (Real.sqrt |(NumberField.discr K : ℝ)| * NumberField.dedekindZeta_residue K) := by
  have hd : Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 :=
    (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K))).ne'
  have hc : (NumberField.classNumber K : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.classNumber_pos K).ne'
  rw [NumberField.dedekindZeta_residue_def,← NumberField.IsTotallyReal.finrank,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero,
    NumberField.Units.torsionOrder_eq_two_of_odd_finrank (hn ▸ hodd),hn]
  simp only [pow_zero,mul_one,Nat.cast_ofNat]
  field_simp

lemma packetUnfoldingCoefficient_ennreal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hn : Module.finrank ℚ K = n) (hodd : Odd n) :
    ((NumberField.classNumber K : ℝ≥0∞)*2^n)⁻¹ *
        (ENNReal.ofReal (NumberField.Units.regulator K))⁻¹ * 2 =
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ := by
  have hc := congrArg ENNReal.ofReal (packetUnfoldingCoefficient hn hodd)
  rw [ENNReal.ofReal_div_of_pos (mul_pos (mul_pos (by exact_mod_cast NumberField.classNumber_pos K) (pow_pos (by norm_num) _)) (NumberField.Units.regulator_pos K)),ENNReal.ofReal_div_of_pos (by
    exact mul_pos (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)))
      (NumberField.dedekindZeta_residue_pos K))] at hc
  simp only [ENNReal.ofReal_ofNat,ENNReal.ofReal_one,one_div] at hc
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat,ENNReal.ofReal_mul (by positivity)] at hc
  rw [← ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl (by finiteness))] 
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hc



lemma allSignedGlobalLabel_card {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    Nat.card (AllSignedGlobalLabel M) =
      NumberField.classNumber K * (Nat.card (globalLabels M 1) * 2^n) := by
  let : Finite (globalLabels M 1) := (globalLabels_finite M hn 1).to_subtype
  let e : AllSignedGlobalLabel M ≃ ClassGroup (𝓞 K) ×
      (globalLabels M 1 × (Fin n → SignTypeˣ)) :=
    (Equiv.sigmaCongrRight (fun c => (signedGlobalLabelEquiv M (classRepresentative K c)).trans
      (Equiv.prodCongr (globalLabelsEquiv M hn (classRepresentative K c) 1) (Equiv.refl _)))).trans
        (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr e,Nat.card_prod,Nat.card_prod,Nat.card_fun,Nat.card_fin]
  have hs : Nat.card SignTypeˣ = 2 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_units]
    decide
  rw [hs,Nat.card_eq_fintype_card]
  rfl

lemma orderedLogFundamentalDomain_volume {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume) :
    volume t = ENNReal.ofReal (NumberField.Units.regulator K) := by
  have hr : (volume t).toReal = NumberField.Units.regulator K :=
    (ZLattice.covolume_eq_measure_fundamentalDomain (orderedLogSubgroup σ ⊤) volume ht).symm.trans
      (orderedLogSubgroup_covolume_eq_regulator σ)
  have htop : volume t ≠ ⊤ := by
    intro h
    apply NumberField.Units.regulator_ne_zero K
    simpa only [h,ENNReal.toReal_top] using hr.symm
  rw [← hr, ENNReal.ofReal_toReal htop]

lemma cancel_label_average {a b L R S : ℝ≥0∞} (hL0 : L ≠ 0) (hLt : L ≠ ⊤) :
    (a*(L*b))⁻¹ * (R⁻¹ * (L*(2*S))) = (a*b)⁻¹ * R⁻¹ * 2 * S := by
  rw [show a*(L*b) = (a*b)*L by ring,ENNReal.mul_inv (Or.inr hLt) (Or.inr hL0)]
  calc
    _ = (a*b)⁻¹ * R⁻¹ * 2 * ((L⁻¹*L)*S) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hL0 hLt,one_mul]

 

lemma allSignedLabel_siegelTransform_lintegral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    [∀ c : ClassGroup (𝓞 K), Fintype (SignedGlobalLabel M (classRepresentative K c))]
    [∀ c : ClassGroup (𝓞 K), Fintype (globalLabels M (classRepresentative K c))]
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑ x : AllSignedGlobalLabel M,
      siegelTransform f (orbitMap (allSignedGlobalLabelPoint M σ hodd x) u)) =
      (Nat.card (globalLabels M 1) : ℝ≥0∞) * (2 *
      ∑' J : integralFractionalIdeals K, globalIdealWeight M J.1 *
        productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) /
          ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|))) := by
  simp only [AllSignedGlobalLabel,Fintype.sum_sigma,allSignedGlobalLabelPoint]
  rw [lintegral_finsetSum Finset.univ (f := fun c u =>
    ∑ x : SignedGlobalLabel M (classRepresentative K c),
      siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd (classRepresentative K c) x) u))
    (fun c _ => Finset.measurable_sum _ (fun x _ =>
      (measurable_siegelTransform hf).comp (continuous_orbitMap _).measurable))]
  simp_rw [signedLabel_siegelTransform_lintegral M σ hn hodd _ ht f hf]
  have hcard (c : ClassGroup (𝓞 K)) :
      Nat.card (globalLabels M (classRepresentative K c)) = Nat.card (globalLabels M 1) :=
    Nat.card_congr (globalLabelsEquiv M hn (classRepresentative K c) 1)
  simp_rw [hcard]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  congr 2
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact tsum_idealClassPartition K (fun J => globalIdealWeight M J *
    productFiberIntegral f ((FractionalIdeal.absNorm J.val : ℝ) /
      ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)))

 

theorem packetMeasure_siegel_unfolding_fractional {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, siegelTransform f x ∂packetMeasure M σ) =
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      ∑' J : integralFractionalIdeals K, globalIdealWeight M J.1 *
        productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) / packetScale M) := by
  let (c : ClassGroup (𝓞 K)) : Finite (SignedGlobalLabel M (classRepresentative K c)) :=
    signedGlobalLabel_finite M hn _
  let (c : ClassGroup (𝓞 K)) : Fintype (SignedGlobalLabel M (classRepresentative K c)) := Fintype.ofFinite _
  let (c : ClassGroup (𝓞 K)) : Fintype (globalLabels M (classRepresentative K c)) :=
    (globalLabels_finite M hn _).fintype
  let b := Module.Free.chooseBasis ℤ (orderedLogSubgroup σ ⊤)
  let t := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ (orderedLogSubgroup σ ⊤) b)
  have ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume :=
    ZLattice.isAddFundamentalDomain b volume
  rw [packetMeasure_lintegral_signedLogAverage M σ hn hodd ht _ (measurable_siegelTransform hf),
    allSignedLabel_siegelTransform_lintegral M σ hn hodd ht f hf,
    orderedLogFundamentalDomain_volume σ ht,allSignedGlobalLabel_card M hn]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [cancel_label_average (by exact_mod_cast (globalLabels_card_pos M hn 1).ne') (by finiteness),
    packetUnfoldingCoefficient_ennreal hn hodd]
  rfl



theorem packetMeasure_siegel_unfolding {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, siegelTransform f x ∂packetMeasure M σ) =
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥}, nonzeroIdealWeight M J *
        productFiberIntegral f ((Ideal.absNorm J.1 : ℝ) / packetScale M) := by
  rw [packetMeasure_siegel_unfolding_fractional M σ hn hodd f hf]
  congr 1
  rw [← (integralFractionalIdealsEquiv K).tsum_eq]
  apply tsum_congr
  intro J
  change nonzeroIdealWeight M J *
    productFiberIntegral f ((FractionalIdeal.absNorm (J.1 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) / packetScale M) = _
  rw [FractionalIdeal.coeIdeal_absNorm,Rat.cast_natCast]

lemma signValue_abs (w : SignTypeˣ) : |signValue w| = 1 := by
  have hw := w.ne_zero
  cases h : (w : SignType) <;> simp_all [signValue]



lemma measurableSet_coordinateBox {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) :
    MeasurableSet (coordinateBox w ε) := by
  simp only [coordinateBox, ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    (isClosed_le (by fun_prop : Continuous (fun v : Fin n → ℝ => |v i-w i|))
      continuous_const).measurableSet)

lemma measurable_boxIndicator {n : ℕ} (w : Fin n → ℝ) (ε : ℝ) :
    Measurable (boxIndicator w ε) :=
  measurable_const.indicator (measurableSet_coordinateBox w ε)

lemma fiberPoint_abs_prod {d : ℕ} (w : Fin (d+1) → SignTypeˣ) (z : ℝ)
    (u : LogCoordinates d) :
    (∏ i, |(Fin.snoc (fun i => signValue (w i.castSucc)*Real.exp (u i))
      (signValue (w (Fin.last d))*z*Real.exp (-∑ i, u i))) i|) = |z| := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,abs_mul,signValue_abs,one_mul,
    abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_sum,← mul_assoc, mul_comm (Real.exp (∑ i, u i)) |z|,
    mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma saturationIndex_le_packetScale {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : (saturationIndex M : ℝ) ≤ packetScale M := by
  have hD : (1:ℝ) ≤ Real.sqrt |(NumberField.discr K : ℝ)| := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (fieldDiscriminant_one_le K)
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hD

lemma nonzeroIdealWeight_eq_global {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : {J : Ideal (𝓞 K) // J ≠ ⊥}) :
    nonzeroIdealWeight M I = globalIdealWeight M (nonzeroIntegralIdealUnit I) := rfl



end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

 

lemma packet_moment_normalization {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (B : ℝ≥0∞) (A : ℝ) (hA : 0 ≤ A) :
    (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ * B *
      (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (A*packetScale M*NumberField.dedekindZeta_residue K) = B*ENNReal.ofReal A := by
  have hD : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (fieldDiscriminant_one_le K))
  have hk := NumberField.dedekindZeta_residue_pos K
  have hQ := (packetScale_pos M).le
  have hqe : ENNReal.ofReal (packetScale M) =
      (saturationIndex M : ℝ≥0∞)*ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) := by
    rw [packetScale,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_mul (mul_nonneg hA hQ),ENNReal.ofReal_mul hA,hqe]
  calc
    _ = ((ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
        (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))) *
        ((saturationIndex M : ℝ≥0∞)⁻¹ * (saturationIndex M : ℝ≥0∞)) * B * ENNReal.ofReal A := by ring
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hD)
        (ENNReal.ofReal_ne_zero_iff.mpr hk)) (ENNReal.mul_ne_top (by finiteness) (by finiteness)),
        ENNReal.inv_mul_cancel (by exact_mod_cast saturationIndex_ne_zero M) (by finiteness),
        one_mul,one_mul]

end PrimeDegreePackets

open Filter Set Topology

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
namespace PrimeDegreePackets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_preimage {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    orthoBox u a = (fun x => WithLp.ofLp (u.repr x)) ⁻¹' Set.Icc (-a) a := by
  ext x
  simp [orthoBox,abs_le,Pi.le_def,forall_and]

lemma orthoBox_volume {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    volume (orthoBox u a) = ∏ i, ENNReal.ofReal (2*a i) := by
  rw [orthoBox_preimage]
  have hp := (PiLp.volume_preserving_ofLp (Fin n)).comp u.measurePreserving_repr
  have H := hp.measure_preimage (measurableSet_Icc.nullMeasurableSet : NullMeasurableSet (Set.Icc (-a) a) volume)
  change volume ((WithLp.ofLp ∘ u.repr) ⁻¹' Set.Icc (-a) a) = _
  rw [H,Real.volume_Icc_pi]
  congr 1
  ext i
  simp [two_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_convex {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ) :
    Convex ℝ (orthoBox u a) := by
  rw [orthoBox_preimage]
  exact (convex_Icc (-a) a).linear_preimage
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toLinearMap.comp u.repr.toLinearMap)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_symmetric {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    {x : E} (hx : x ∈ orthoBox u a) : -x ∈ orthoBox u a := by
  intro i
  simpa using hx i

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_norm_le {n : ℕ} (u : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    {x : E} (hx : x ∈ orthoBox u a) : ‖x‖ ≤ ∑ i, a i := by
  calc
    ‖x‖ = ‖∑ i, u.repr x i • u i‖ := by rw [u.sum_repr]
    _ ≤ ∑ i, ‖u.repr x i • u i‖ := norm_sum_le _ _
    _ = ∑ i, |u.repr x i| := by simp [norm_smul,u.orthonormal.1,Real.norm_eq_abs]
    _ ≤ ∑ i, a i := Finset.sum_le_sum (fun i _ => hx i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma orthoBox_norm_le_of_zero_first {n : ℕ} (u : OrthonormalBasis (Fin (n+1)) ℝ E)
    (a : Fin (n+1) → ℝ) {x : E} (hx : x ∈ orthoBox u a) (hzero : u.repr x 0 = 0) :
    ‖x‖ ≤ ∑ i : Fin n, a i.succ := by
  calc
    ‖x‖ = ‖∑ i : Fin n, u.repr x i.succ • u i.succ‖ := by
      have H := u.sum_repr x
      rw [Fin.sum_univ_succ,hzero,zero_smul,zero_add] at H
      exact congrArg norm H.symm
    _ ≤ ∑ i : Fin n, ‖u.repr x i.succ • u i.succ‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |u.repr x i.succ| := by simp [norm_smul,u.orthonormal.1,Real.norm_eq_abs]
    _ ≤ ∑ i : Fin n, a i.succ := Finset.sum_le_sum (fun i _ => hx i.succ)

omit [MeasurableSpace E] [BorelSpace E] in
 

lemma exists_orthonormal_first_perp {n : ℕ} (hdim : finrank ℝ E = n+1)
    (W : Submodule ℝ E) (hW : W ≠ ⊤) :
    ∃ u : OrthonormalBasis (Fin (n+1)) ℝ E, ∀ x ∈ W, u.repr x 0 = 0 := by
  have hperp : Wᗮ ≠ ⊥ := fun h => hW (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    simp [w,norm_smul,hv0]
  have hwW : w ∈ Wᗮ := Wᗮ.smul_mem _ hv
  have H : Orthonormal ℝ (({0} : Set (Fin (n+1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (i.property.trans j.property.symm)
    subst j
    simp [hw]
  obtain ⟨u,hu⟩ := H.exists_orthonormalBasis_extension_of_card_eq (by simpa using hdim)
  refine ⟨u,?_⟩
  intro x hx
  rw [u.repr_apply_apply,hu 0 (by simp)]
  exact (real_inner_comm _ _).trans ((Submodule.mem_orthogonal _ _).mp hwW x hx)

 

theorem bounded_vector_outside_subspace {n : ℕ} (hdim : finrank ℝ E = n+1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) = 1 →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → ε ≤ ‖v‖) →
      ∀ W : Submodule ℝ E, W ≠ ⊤ →
        ∃ v ∈ Submodule.span ℤ (Set.range b), v ∉ W ∧ ‖v‖ ≤ B := by
  let s : ℝ := min 1 (ε / (2*(n+1)))
  have hs : 0 < s := lt_min zero_lt_one (div_pos hε (by positivity))
  let R : ℝ := 2/s^n
  have hR : 0 < R := div_pos (by norm_num) (pow_pos hs _)
  refine ⟨R+(n:ℝ)*s,by positivity,?_⟩
  intro b hb hshort W hW
  obtain ⟨u,hu⟩ := exists_orthonormal_first_perp hdim W hW
  let a : Fin (n+1) → ℝ := Fin.cons R (fun _ => s)
  have hvol : (volume (ZSpan.fundamentalDomain b))*2^(finrank ℝ E) <
      volume (orthoBox u a) := by
    rw [hb,one_mul,hdim,orthoBox_volume,Fin.prod_univ_succ]
    simp only [a,Fin.cons_zero,Fin.cons_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*s),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R)]
    have H : (2*R)*(2*s)^n = (2:ℝ)^(n+1)*2 := by
      dsimp [R]
      rw [mul_pow,pow_succ]
      field_simp
    rw [H,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    simpa only [mul_one] using ENNReal.mul_lt_mul_right
      (by positivity : (2:ℝ≥0∞)^(n+1) ≠ 0) (by finiteness) (by norm_num : (1:ℝ≥0∞) < 2)
  let L := Submodule.span ℤ (Set.range b)
  have : Countable L := inferInstance
  obtain ⟨v,hv0,hv⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := L.toAddSubgroup)
    (ZSpan.isAddFundamentalDomain b volume) (fun x hx => orthoBox_symmetric u a hx)
    (orthoBox_convex u a) hvol
  have hvE : (v : E) ≠ 0 := by exact_mod_cast hv0
  refine ⟨v,v.property,?_,?_⟩
  · intro hvW
    have H := orthoBox_norm_le_of_zero_first u a hv (hu _ hvW)
    simp only [a,Fin.cons_succ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul] at H
    have hsε : s ≤ ε/(2*(n+1)) := min_le_right _ _
    have Hs : (n:ℝ)*s < ε := by
      have Hn : (n:ℝ)*s ≤ ((n:ℝ)+1)*s := by nlinarith
      have Hs : ((n:ℝ)+1)*s ≤ ε/2 := by
        have := (le_div_iff₀ (by positivity : 0 < 2*((n:ℝ)+1))).mp hsε
        nlinarith
      linarith
    exact (hshort v v.property hvE).not_gt (lt_of_le_of_lt H Hs)
  · have H := orthoBox_norm_le u a hv
    simpa [a,Fin.sum_univ_succ] using H

 

theorem bounded_real_basis_in_lattice {n : ℕ} (hdim : finrank ℝ E = n+1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ b : Basis (Fin (n+1)) ℝ E,
      volume (ZSpan.fundamentalDomain b) = 1 →
      (∀ v ∈ Submodule.span ℤ (Set.range b), v ≠ 0 → ε ≤ ‖v‖) →
      ∃ c : Basis (Fin (n+1)) ℝ E,
        ∀ i, c i ∈ Submodule.span ℤ (Set.range b) ∧ ‖c i‖ ≤ B := by
  obtain ⟨B,hB,H⟩ := bounded_vector_outside_subspace hdim ε hε
  refine ⟨B,hB,?_⟩
  intro b hb hshort
  let S : Set E := {x | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ B}
  have hsp : Submodule.span ℝ S = ⊤ := by
    by_contra hne
    obtain ⟨v,hv,hvW,hvB⟩ := H b hb hshort (Submodule.span ℝ S) hne
    exact hvW (Submodule.subset_span (show v ∈ S from ⟨hv,hvB⟩))
  obtain ⟨T,hTS,hTspan,hTind⟩ := exists_linearIndependent ℝ S
  have hTtop : Submodule.span ℝ T = ⊤ := hTspan.trans hsp
  let c₀ : Basis T ℝ E := Basis.mk hTind (by
    rw [Subtype.range_coe_subtype]
    change ⊤ ≤ Submodule.span ℝ T
    rw [hTtop])
  have : Finite T := hTind.finite
  let : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T = n+1 := (finrank_eq_card_basis c₀).symm.trans hdim
  let e : T ≃ Fin (n+1) := Fintype.equivFinOfCardEq hcard
  refine ⟨c₀.reindex e,?_⟩
  intro i
  have H := hTS (e.symm i).property
  simpa [c₀,Basis.coe_reindex,S] using H

open scoped Matrix
open Matrix

lemma euclideanRowBasis_volume {n : ℕ} (g : G n) :
    volume (ZSpan.fundamentalDomain (euclideanRowBasis g)) = 1 := by
  let u := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hi : u.toLinearEquiv '' ZSpan.fundamentalDomain (euclideanRowBasis g) =
      ZSpan.fundamentalDomain (rowBasis g) := by
    rw [ZSpan.map_fundamentalDomain]
    congr 1
  have hp : u ⁻¹' ZSpan.fundamentalDomain (rowBasis g) =
      ZSpan.fundamentalDomain (euclideanRowBasis g) := by
    rw [← hi]
    exact Set.preimage_image_eq _ u.injective
  have hm := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (ZSpan.fundamentalDomain_measurableSet (rowBasis g)).nullMeasurableSet
  change volume (u ⁻¹' ZSpan.fundamentalDomain (rowBasis g)) = _ at hm
  rw [hp,ZSpan.volume_fundamentalDomain] at hm
  have hr : Matrix.of (rowBasis g) = g.1 := by ext i j; exact rowBasis_apply g i j
  simpa [hr,g.2] using hm

lemma sum_euclideanRowBasis {n : ℕ} (g : G n) (z : Fin n → ℤ) :
    ∑ i, z i • euclideanRowBasis g i =
      WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1) := by
  ext j
  simp [Matrix.vecMul,dotProduct,← Int.cast_smul_eq_zsmul ℝ]

 

theorem bounded_independent_rows (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ g : G (n+1),
      (∀ z : Fin (n+1) → ℤ, z ≠ 0 →
        ε ≤ ‖WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)‖) →
      ∃ Z : Matrix (Fin (n+1)) (Fin (n+1)) ℤ,
        Z.det ≠ 0 ∧ ∀ i j, |((Z.map (Int.castRingHom ℝ))*g.1) i j| ≤ B := by
  obtain ⟨B,hB,H⟩ := bounded_real_basis_in_lattice
    (E := EuclideanSpace ℝ (Fin (n+1))) (n := n) (by simp) ε hε
  refine ⟨B,hB,?_⟩
  intro g hg
  have hshort : ∀ v ∈ Submodule.span ℤ (Set.range (euclideanRowBasis g)),
      v ≠ 0 → ε ≤ ‖v‖ := by
    intro v hv hv0
    obtain ⟨z,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
    have hz : z ≠ 0 := by intro hz; simp [hz] at hv0
    rw [sum_euclideanRowBasis]
    exact hg z hz
  obtain ⟨c,hc⟩ := H (euclideanRowBasis g) (euclideanRowBasis_volume g) hshort
  choose Z hZ using (fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hc i).1)
  let V : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun i j => (c i).ofLp j
  have hV : V = (Matrix.of Z).map (Int.castRingHom ℝ)*g.1 := by
    ext i j
    have H := congrArg (fun v : EuclideanSpace ℝ (Fin (n+1)) => v.ofLp j) (hZ i)
    rw [sum_euclideanRowBasis] at H
    exact H.symm
  have hdetV : V.det ≠ 0 := by
    let c' := c.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)).toLinearEquiv
    have H := ((Pi.basisFun ℝ (Fin (n+1))).isUnit_det c').ne_zero
    have he : (Pi.basisFun ℝ (Fin (n+1))).det c' = V.det := by
      rw [Basis.det_apply,← Matrix.det_transpose]
      rfl
    rwa [he] at H
  refine ⟨Matrix.of Z,?_,?_⟩
  · intro hz
    apply hdetV
    rw [hV,Matrix.det_mul]
    have H : ((Matrix.of Z).map (Int.castRingHom ℝ)).det = ((Matrix.of Z).det : ℝ) :=
      (Int.cast_det (Matrix.of Z)).symm
    rw [H,hz]
    simp
  · intro i j
    rw [← hV]
    exact (PiLp.norm_apply_le (c i) j).trans (hc i).2



lemma coordinateMod_ker {n m : ℕ} (v : Fin n → ℤ) :
    v ∈ (coordinateMod n m).ker ↔ ∃ w : Fin n → ℤ, v = (m:ℤ) • w := by
  change ((fun i => (v i : ZMod m)) = 0) ↔ _
  constructor
  · intro hv
    have hd (i : Fin n) : (m:ℤ) ∣ v i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hv i)
    choose w hw using hd
    exact ⟨w,funext hw⟩
  · rintro ⟨w,rfl⟩
    ext i
    simp

lemma finite_integral_submodules_above_mod (n m : ℕ) (hm : m ≠ 0) :
    {L : Submodule ℤ (Fin n → ℤ) | (coordinateMod n m).ker ≤ L}.Finite := by
  let : NeZero m := ⟨hm⟩
  let F := coordinateMod n m
  have : Finite {L : Submodule ℤ (Fin n → ℤ) // F.ker ≤ L} :=
    Finite.of_injective (fun L : {L : Submodule ℤ (Fin n → ℤ) // F.ker ≤ L} => L.val.map F)
      (by
        intro L M h
        apply Subtype.ext
        have H := congrArg (Submodule.comap F) h
        simpa only [Submodule.comap_map_eq,sup_eq_left.mpr L.property,
          sup_eq_left.mpr M.property] using H)
  exact Set.finite_coe_iff.mp this



lemma det_smul_mem_columnModule {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : A.det • v ∈ columnModule A := by
  refine ⟨A.adjugate.mulVec v,?_⟩
  change A.mulVec (A.adjugate.mulVec v) = _
  rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]

lemma coordinateMod_ker_le_columnModule {n N : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) (hN : A.det.natAbs ≤ N) :
    (coordinateMod n (N.factorial)).ker ≤ columnModule A := by
  have hd : A.det ∣ (N.factorial:ℤ) := Int.natAbs_dvd_natAbs.mp (by
    simpa using Nat.dvd_factorial (Int.natAbs_pos.mpr hA) hN)
  obtain ⟨k,hk⟩ := hd
  intro v hv
  obtain ⟨w,rfl⟩ := (coordinateMod_ker v).mp hv
  rw [hk,mul_smul]
  exact det_smul_mem_columnModule A (k • w)

 

theorem finite_bounded_column_modules (n N : ℕ) :
    {L : Submodule ℤ (Fin n → ℤ) | ∃ A : Matrix (Fin n) (Fin n) ℤ,
      A.det ≠ 0 ∧ A.det.natAbs ≤ N ∧ columnModule A = L}.Finite := by
  apply (finite_integral_submodules_above_mod n N.factorial (Nat.factorial_ne_zero N)).subset
  rintro L ⟨A,hA,hN,rfl⟩
  exact coordinateMod_ker_le_columnModule A hA hN

lemma exists_int_matrix_of_columnModule_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (hAB : columnModule A ≤ columnModule B) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, A = B*C := by
  have hcol (j : Fin n) : (fun i => A i j) ∈ columnModule A := by
    refine ⟨Pi.single j 1,?_⟩
    change A.mulVec (Pi.single j 1) = _
    ext i
    simp [Matrix.mulVec,dotProduct,Pi.single_apply]
  have H (j : Fin n) : ∃ v : Fin n → ℤ, B.mulVec v = fun i => A i j := hAB (hcol j)
  choose C hC using H
  refine ⟨Matrix.transpose C,?_⟩
  ext i j
  have H := congrFun (hC j) i
  exact H.symm



lemma exists_SL_of_signed_columnModule_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℤ) (_hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hsign : 0 < A.det ↔ 0 < B.det) (hAB : columnModule A = columnModule B) :
    ∃ C : Matrix.SpecialLinearGroup (Fin n) ℤ, A = B*C.1 := by
  obtain ⟨C,hC⟩ := exists_int_matrix_of_columnModule_le A B hAB.le
  obtain ⟨D,hD⟩ := exists_int_matrix_of_columnModule_le B A hAB.symm.le
  have hdC : A.det = B.det*C.det := by rw [hC,Matrix.det_mul]
  have hdD : B.det = A.det*D.det := by rw [hD,Matrix.det_mul]
  have hCD : C.det*D.det = 1 := by
    apply mul_left_cancel₀ hB
    linear_combination -(hdC*D.det+hdD)
  have hu : IsUnit C.det := isUnit_iff_dvd_one.mpr ⟨D.det,hCD.symm⟩
  have hC1 : C.det = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · rw [h] at hdC
      by_cases hpos : 0 < A.det
      · have := hsign.mp hpos
        omega
      · have := mt hsign.mpr hpos
        omega
  exact ⟨⟨C,hC1⟩,hC⟩

 

theorem finite_bounded_nonsingular_matrix_representatives (n N : ℕ) :
    ∃ s : Finset (Matrix (Fin n) (Fin n) ℤ),
      (∀ B ∈ s, B.det ≠ 0) ∧
      ∀ A : Matrix (Fin n) (Fin n) ℤ, A.det ≠ 0 → A.det.natAbs ≤ N →
        ∃ B ∈ s, ∃ C : Matrix.SpecialLinearGroup (Fin n) ℤ, A = B*C.1 := by
  classical
  let S : Set (Submodule ℤ (Fin n → ℤ) × Bool) :=
    {L | ∃ A : Matrix (Fin n) (Fin n) ℤ, A.det ≠ 0 ∧ A.det.natAbs ≤ N ∧
      columnModule A = L.1 ∧ decide (0 < A.det) = L.2}
  have hS : S.Finite :=
    ((finite_bounded_column_modules n N).prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset (by
      rintro ⟨L,b⟩ ⟨A,hA,hN,hL,hb⟩
      exact ⟨⟨A,hA,hN,hL⟩,Set.mem_univ _⟩)
  let : Fintype S := hS.fintype
  choose B hB using (fun L : S => L.property)
  refine ⟨Finset.univ.image B,?_,?_⟩
  · intro A hA
    obtain ⟨L,_,rfl⟩ := Finset.mem_image.mp hA
    exact (hB L).1
  · intro A hA hN
    let L : S := ⟨(columnModule A,decide (0 < A.det)),⟨A,hA,hN,rfl,rfl⟩⟩
    refine ⟨B L,Finset.mem_image.mpr ⟨L,Finset.mem_univ _,rfl⟩,?_⟩
    apply exists_SL_of_signed_columnModule_eq A (B L) hA (hB L).1
    · have H := (hB L).2.2.2
      change decide (0 < (B L).det) = decide (0 < A.det) at H
      by_cases hpos : 0 < A.det
      · simp only [hpos,decide_true] at H
        exact iff_of_true hpos (of_decide_eq_true H)
      · simp only [hpos,decide_false] at H
        exact iff_of_false hpos (of_decide_eq_false H)
    · exact (hB L).2.2.1.symm

 

theorem bounded_SL_representatives (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ), IsCompact K ∧
      ∀ g : G (n+1),
        (∀ z : Fin (n+1) → ℤ, z ≠ 0 →
          ε ≤ ‖WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)‖) →
        ∃ C : Matrix.SpecialLinearGroup (Fin (n+1)) ℤ,
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C)*g).1 ∈ K := by
  classical
  obtain ⟨B,hB,H⟩ := bounded_independent_rows n ε hε
  let K₀ : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
    (Set.Icc (fun _ _ => -B) (fun _ _ => B) : Set (Fin (n+1) → Fin (n+1) → ℝ))
  have hK₀ : IsCompact K₀ := isCompact_Icc (α := Fin (n+1) → Fin (n+1) → ℝ)
  obtain ⟨D,hD⟩ := hK₀.bddAbove_image (continuous_id.matrix_det.abs.continuousOn)
  obtain ⟨N,hN⟩ := exists_nat_gt D
  obtain ⟨s,hs,Hs⟩ := finite_bounded_nonsingular_matrix_representatives (n+1) N
  let K : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
    ⋃ A ∈ (s : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℤ)),
      (fun V => (A.map (Int.castRingHom ℝ))⁻¹ * V) '' K₀
  have hK : IsCompact K := s.finite_toSet.isCompact_biUnion (fun A _ =>
    hK₀.image (continuous_const.matrix_mul continuous_id))
  refine ⟨K,hK,?_⟩
  intro g hg
  obtain ⟨Z,hZ,hZB⟩ := H g hg
  have hV : Z.map (Int.castRingHom ℝ)*g.1 ∈ K₀ := by
    show (∀ i j, -B ≤ (Z.map (Int.castRingHom ℝ)*g.1) i j) ∧
      (∀ i j, (Z.map (Int.castRingHom ℝ)*g.1) i j ≤ B)
    exact ⟨fun i j => (abs_le.mp (hZB i j)).1,fun i j => (abs_le.mp (hZB i j)).2⟩
  have hZN : Z.det.natAbs ≤ N := by
    have hd := hD (Set.mem_image_of_mem (fun V => |V.det|) hV)
    have he : (Z.map (Int.castRingHom ℝ)*g.1).det = (Z.det : ℝ) := by
      rw [Matrix.det_mul,g.2,mul_one]
      exact (Int.cast_det Z).symm
    rw [he] at hd
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_natAbs,Int.cast_abs]
    exact hd.trans hN.le
  obtain ⟨A,hA,C,hC⟩ := Hs Z hZ hZN
  refine ⟨C,?_⟩
  apply Set.mem_iUnion_of_mem A
  apply Set.mem_iUnion_of_mem hA
  refine ⟨Z.map (Int.castRingHom ℝ)*g.1,hV,?_⟩
  have hA0 : IsUnit (A.map (Int.castRingHom ℝ)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [show (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) from (Int.cast_det A).symm]
    exact_mod_cast hs A hA
  have hmap : Z.map (Int.castRingHom ℝ) =
      A.map (Int.castRingHom ℝ) * C.1.map (Int.castRingHom ℝ) := by
    rw [hC]
    exact Matrix.map_mul
  change (A.map (Int.castRingHom ℝ))⁻¹ * (Z.map (Int.castRingHom ℝ)*g.1) =
    C.1.map (Int.castRingHom ℝ)*g.1
  rw [hmap,← Matrix.mul_assoc,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hA0,
    Matrix.one_mul]

open TopologicalSpace
open scoped Topology



theorem mahler_compact (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IsCompact (thickLattices (n+1) ε) := by
  obtain ⟨K,hK,H⟩ := bounded_SL_representatives n ε hε
  have hpre : IsCompact (Subtype.val ⁻¹' K : Set (G (n+1))) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hK
  have himage := hpre.image
    (continuous_quotient_mk' : Continuous
      (Quotient.mk (QuotientGroup.rightRel (integralGroup (n+1)))))
  apply himage.of_isClosed_subset (thickLattices_isClosed (n+1) ε)
  intro x hx
  induction x using Quotient.inductionOn with
  | h g =>
    have hshort : ∀ z : Fin (n+1) → ℤ, z ≠ 0 →
        ε ≤ ‖WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)‖ := by
      intro z hz
      refine (hx g rfl z hz).trans ?_
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact PiLp.norm_apply_le (WithLp.toLp 2 ((fun i => (z i : ℝ)) ᵥ* g.1)) i
    obtain ⟨C,hC⟩ := H g hshort
    refine ⟨(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C)*g,hC,?_⟩
    apply Quotient.sound
    change (QuotientGroup.rightRel (integralGroup (n+1)))
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) C)*g) g
    rw [QuotientGroup.rightRel_apply]
    refine ⟨C⁻¹, ?_⟩
    simp

lemma packetSupport_isCompact {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    (hodd : Odd (d+1)) : IsCompact (packetSupport M σ) := by
  let : Fintype (packetOrbits M σ) := (packetOrbits_finite M σ hn hodd).fintype
  exact isCompact_iUnion (fun O => packetOrbit_isCompact hn hodd O)

lemma orbitProbability_compl_range {d : ℕ} (x : X (d+1))
    {s : Set (X (d+1))} (hs : MeasurableSet s) (hr : diagonalOrbit x ⊆ s) :
    orbitProbability x sᶜ = 0 := by
  rw [orbitProbability,Measure.smul_apply,orbitalHaar]
  split_ifs
  · rw [Measure.map_apply (continuous_orbitMap x).measurable hs.compl]
    have H : orbitMap x ⁻¹' sᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hu (hr ⟨u,rfl⟩)
    rw [H,measure_empty,smul_zero]
  · simp

 

theorem packetMeasure_compl_support {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K)
    (σ : OrderedEmbeddings (d+1) K) (hn : Module.finrank ℚ K = d+1)
    (hodd : Odd (d+1)) : packetMeasure M σ (packetSupport M σ)ᶜ = 0 := by
  have hs := (packetSupport_isCompact M σ hn hodd).isClosed.measurableSet
  rw [packetMeasure,Measure.smul_apply,Measure.sum_apply _ hs.compl]
  have H (O : packetOrbits M σ) : orbitProbability (orbitBasepoint O) (packetSupport M σ)ᶜ = 0 := by
    apply orbitProbability_compl_range _ hs
    rw [orbitBasepoint_spec]
    exact Set.subset_iUnion (fun O : packetOrbits M σ => O.1) O
  simp only [Measure.smul_apply,H,smul_zero,tsum_zero]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_CuspMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology Matrix
open scoped ENNReal BigOperators Classical

 

lemma cusp_indicator_le_siegel {n : ℕ} {θ : ℝ} (x : X n) :
    (thickLattices n θ)ᶜ.indicator (fun _ => (1:ℝ≥0∞)) x ≤
      siegelTransform (boxIndicator (fun _ : Fin n => 0) θ) x := by
  by_cases hx : x ∈ (thickLattices n θ)ᶜ
  · rw [Set.indicator_of_mem hx]
    obtain ⟨g,hg,z,hz,hzθ⟩ : ∃ g : G n,
        Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x ∧
          ∃ z : Fin n → ℤ, z ≠ 0 ∧ ‖(fun i => (z i:ℝ)) ᵥ* g.1‖ < θ := by
      simpa only [thickLattices,Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall,
        Classical.not_imp,not_le,exists_prop] using hx
    rw [← hg,siegelTransform_mk]
    have hv : integerRowMap g.1 z ∈ coordinateBox (fun _ => 0) θ := by
      intro j
      rw [integerRowMap_apply,sub_zero]
      exact (show |((fun i => (z i:ℝ)) ᵥ* g.1) j| ≤
        ‖(fun i => (z i:ℝ)) ᵥ* g.1‖ by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm ((fun i => (z i:ℝ)) ᵥ* g.1) j).trans hzθ.le
    have H := ENNReal.le_tsum (f := fun v : {z : Fin n → ℤ // z ≠ 0} =>
      boxIndicator (fun _ => 0) θ (integerRowMap g.1 v.1)) ⟨z,hz⟩
    simpa only [boxIndicator,Set.indicator_of_mem hv] using H
  · rw [Set.indicator_of_notMem hx]
    exact bot_le

lemma cusp_mass_le_cube_moment {n : ℕ} (μ : Measure (X n)) (θ : ℝ) :
    μ (thickLattices n θ)ᶜ ≤
      ∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin n => 0) θ) x ∂μ := by
  calc
    _ = ∫⁻ x, (thickLattices n θ)ᶜ.indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator (thickLattices_isClosed n θ).isOpen_compl.measurableSet]
      simp
    _ ≤ _ := lintegral_mono cusp_indicator_le_siegel



end PrimeDegreePackets


namespace PrimeDegreePackets



lemma logMoment_summable (d : ℕ) :
    Summable (fun j : ℕ => ((j : ℝ)+1)^d * Real.exp (-(j : ℝ))) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
    (r := Real.exp (-1)) (by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by norm_num))
  have H := (summable_nat_add_iff 1).mpr h
  have H' := H.mul_right (Real.exp 1)
  apply H'.congr
  intro j
  simp only [Nat.cast_add,Nat.cast_one]
  rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
  congr 2
  push_cast
  ring

lemma logMomentConstant_nonneg (d : ℕ) : 0 ≤ logMomentConstant d :=
  tsum_nonneg (fun _ => by positivity)

lemma logarithmic_shell {X r : ℝ} (hX : 0 < X) (hr : 0 < r) (hrX : r ≤ X) :
    let j := ⌊Real.log (X/r)⌋₊
    Real.log (X/r) < (j : ℝ)+1 ∧ r ≤ X*Real.exp (-(j : ℝ)) := by
  have hlog : 0 ≤ Real.log (X/r) := Real.log_nonneg ((le_div_iff₀ hr).mpr (by simpa))
  let j := ⌊Real.log (X/r)⌋₊
  refine ⟨Nat.lt_floor_add_one _,?_⟩
  have H := Real.exp_le_exp.mpr (Nat.floor_le hlog)
  rw [Real.exp_log (div_pos hX hr)] at H
  have H' : r * Real.exp (j : ℝ) ≤ X := by
    simpa [mul_comm] using (le_div_iff₀ hr).mp H
  rw [Real.exp_neg,← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr H'

 

theorem log_weighted_sum_le {α : Type*} (S : Finset α) (N w : α → ℝ)
    (d : ℕ) (X A : ℝ) (hX : 0 < X) (hA : 0 ≤ A)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hN : ∀ a ∈ S, 0 < N a ∧ N a ≤ X)
    (hcount : ∀ t : ℝ, 0 ≤ t → t ≤ X →
      (∑ a ∈ S.filter (fun a => N a ≤ t), w a) ≤ A*t) :
    (∑ a ∈ S, w a * (Real.log (X/N a))^d) ≤ A*X*logMomentConstant d := by
  classical
  let k : α → ℕ := fun a => ⌊Real.log (X/N a)⌋₊
  have hk (a : α) (ha : a ∈ S) := logarithmic_shell hX (hN a ha).1 (hN a ha).2
  have hlogs (a : α) (ha : a ∈ S) : 0 ≤ Real.log (X/N a) :=
    Real.log_nonneg ((le_div_iff₀ (hN a ha).1).mpr (by simpa using (hN a ha).2))
  calc
    _ ≤ ∑ a ∈ S, w a * ((k a : ℝ)+1)^d := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hlogs a ha) (hk a ha).1.le d) (hw a ha)
    _ = ∑ j ∈ S.image k, ∑ a ∈ S.filter (fun a => k a = j), w a * ((k a : ℝ)+1)^d := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image k) (g := k)
        (fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩) _
    _ ≤ ∑ j ∈ S.image k, A*X*(((j : ℝ)+1)^d * Real.exp (-(j : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hfilter : S.filter (fun a => k a = j) ⊆
          S.filter (fun a => N a ≤ X*Real.exp (-(j : ℝ))) := by
        intro a ha
        obtain ⟨ha,hka⟩ := Finset.mem_filter.mp ha
        refine Finset.mem_filter.mpr ⟨ha,?_⟩
        simpa only [← hka] using (hk a ha).2
      have hc := hcount (X*Real.exp (-(j : ℝ))) (by positivity) (by
        apply mul_le_of_le_one_right hX.le
        apply Real.exp_le_one_iff.mpr
        exact neg_nonpos.mpr (Nat.cast_nonneg j))
      have hwf : (∑ a ∈ S.filter (fun a => k a = j), w a) ≤
          A*(X*Real.exp (-(j : ℝ))) := by
        apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hfilter ?_) hc
        intro a ha _
        exact hw a (Finset.mem_filter.mp ha).1
      have he : (∑ a ∈ S.filter (fun a => k a = j), w a * ((k a : ℝ)+1)^d) =
          ((j : ℝ)+1)^d * (∑ a ∈ S.filter (fun a => k a = j), w a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
        ring
      rw [he]
      have H := mul_le_mul_of_nonneg_left hwf (show 0 ≤ ((j : ℝ)+1)^d by positivity)
      convert H using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = A*X*(∑ j ∈ S.image k, ((j : ℝ)+1)^d * Real.exp (-(j : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ A*X*logMomentConstant d := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hX.le)
      exact (logMoment_summable d).sum_le_tsum _ (fun _ _ => by positivity)

 

theorem log_weighted_sum_cutoff {α : Type*} (S : Finset α) (N w : α → ℝ)
    (d : ℕ) (X U Q A : ℝ) (hX : 0 < X) (hA : 0 ≤ A)
    (hQ : 1 ≤ Q) (hXQ : X ≤ Q)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hN : ∀ a ∈ S, 1 ≤ N a ∧ N a ≤ X)
    (hcount : ∀ t : ℝ, U ≤ t →
      (∑ a ∈ S.filter (fun a => N a ≤ t), w a) ≤ A*t) :
    (∑ a ∈ S, w a * (Real.log (X/N a))^d) ≤
      A*U*(Real.log Q)^d + A*X*logMomentConstant d := by
  classical
  have hQ0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlog (a : α) (ha : a ∈ S) :
      0 ≤ Real.log (X/N a) ∧ Real.log (X/N a) ≤ Real.log Q := by
    have ha0 : 0 < N a := lt_of_lt_of_le zero_lt_one (hN a ha).1
    refine ⟨Real.log_nonneg ((le_div_iff₀ ha0).mpr (by simpa using (hN a ha).2)),?_⟩
    apply Real.log_le_log (div_pos hX ha0)
    apply (div_le_iff₀ ha0).mpr
    exact le_trans hXQ (le_mul_of_one_le_right (by linarith) (hN a ha).1)
  have hsmall : (∑ a ∈ S.filter (fun a => N a ≤ U),
      w a * (Real.log (X/N a))^d) ≤ A*U*(Real.log Q)^d := by
    calc
      _ ≤ ∑ a ∈ S.filter (fun a => N a ≤ U), w a * (Real.log Q)^d := by
        apply Finset.sum_le_sum
        intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hlog a haS).1 (hlog a haS).2 d) (hw a haS)
      _ = (∑ a ∈ S.filter (fun a => N a ≤ U), w a) * (Real.log Q)^d := by
        rw [Finset.sum_mul]
      _ ≤ A*U*(Real.log Q)^d := mul_le_mul_of_nonneg_right (hcount U le_rfl) (by positivity)
  have hlarge : (∑ a ∈ S.filter (fun a => ¬ N a ≤ U),
      w a * (Real.log (X/N a))^d) ≤ A*X*logMomentConstant d := by
    apply log_weighted_sum_le _ N w d X A hX hA
    · intro a ha
      exact hw a (Finset.mem_filter.mp ha).1
    · intro a ha
      have haS := (Finset.mem_filter.mp ha).1
      exact ⟨lt_of_lt_of_le zero_lt_one (hN a haS).1,(hN a haS).2⟩
    · intro t ht _
      by_cases hUt : U ≤ t
      · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hcount t hUt)
        · intro a ha
          obtain ⟨ha,hat⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,hat⟩
        · intro a ha _
          exact hw a (Finset.mem_filter.mp ha).1
      · have he : (S.filter (fun a => ¬ N a ≤ U)).filter (fun a => N a ≤ t) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro a ha hat
          exact (Finset.mem_filter.mp ha).2 (le_trans hat (le_of_not_ge hUt))
        rw [he,Finset.sum_empty]
        exact mul_nonneg hA ht
  rw [← Finset.sum_filter_add_sum_filter_not S (fun a => N a ≤ U)]
  exact add_le_add hsmall hlarge

lemma cusp_log_error_vanishes (d : ℕ) :
    Tendsto (fun Q : ℝ => (Real.log Q)^d / Q^((1:ℝ)/4)) atTop (𝓝 0) := by
  have H := (isLittleO_log_rpow_rpow_atTop (d : ℝ)
    (by norm_num : (0:ℝ) < 1/4)).tendsto_div_nhds_zero
  simpa only [Real.rpow_natCast] using H

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set
open scoped ENNReal BigOperators Classical

lemma cube_fiber_log_rectangle {d : ℕ} {θ z : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (s : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d)
    (hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
      (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈
      coordinateBox (fun _ => 0) θ) :
    u ∈ Set.Icc (fun _ => Real.log θ-Real.log (θ^(d+1)/z)) (fun _ => Real.log θ) := by
  have hup (i : Fin d) : u i ≤ Real.log θ := by
    have H := hu i.castSucc
    simp only [Fin.snoc_castSucc,sub_zero,abs_mul,signValue_abs,one_mul,
      abs_of_pos (Real.exp_pos _)] at H
    exact (Real.le_log_iff_exp_le hθ).mpr H
  have hlast : Real.log z - ∑ i, u i ≤ Real.log θ := by
    have H := hu (Fin.last d)
    simp only [Fin.snoc_last,sub_zero,abs_mul,signValue_abs,one_mul,
      abs_of_pos hz,abs_of_pos (Real.exp_pos _)] at H
    have Hlog := Real.log_le_log (mul_pos hz (Real.exp_pos _)) H
    simpa only [Real.log_mul hz.ne' (Real.exp_ne_zero _),Real.log_exp,sub_eq_add_neg]
      using Hlog
  have hsum : ∑ i, (Real.log θ-u i) ≤ Real.log (θ^(d+1)/z) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Real.log_div (pow_ne_zero _ hθ.ne') hz.ne',Real.log_pow,Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨?_,hup⟩
  intro i
  have H := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sub_nonneg.mpr (hup j))
    (Finset.mem_univ i)
  have := H.trans hsum
  linarith

lemma cube_fiber_product_le {d : ℕ} {θ z : ℝ} (hz : 0 ≤ z) (s : Fin (d+1) → SignTypeˣ)
    (u : LogCoordinates d)
    (hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
      (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈
      coordinateBox (fun _ => 0) θ) : z ≤ θ^(d+1) := by
  let v : Fin (d+1) → ℝ := Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
    (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i))
  have H : (∏ i, |v i|) ≤ ∏ _i : Fin (d+1), θ :=
    Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => abs_nonneg (v i))
      (fun i (_ : i ∈ Finset.univ) => by simpa only [sub_zero] using hu i)
  dsimp only [v] at H
  simpa only [fiberPoint_abs_prod,abs_of_nonneg hz,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin] using H

 

theorem productFiberIntegral_cube_eq_zero {d : ℕ} {θ z : ℝ} (hz : 0 ≤ z)
    (hzt : θ^(d+1) < z) :
    productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ) z = 0 := by
  unfold productFiberIntegral
  apply Finset.sum_eq_zero
  intro s _
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro u
  have hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
      (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∉ coordinateBox (fun _ => 0) θ :=
    fun H => (cube_fiber_product_le hz s u H).not_gt hzt
  simp only [boxIndicator,Set.indicator_of_notMem hu,Pi.zero_apply]

 

theorem productFiberIntegral_cube_le {d : ℕ} {θ z : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (hzt : z ≤ θ^(d+1)) :
    productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ) z ≤
      (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) *
        ENNReal.ofReal ((Real.log (θ^(d+1)/z))^d) := by
  let L := Real.log (θ^(d+1)/z)
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hz).mpr hzt)
  let a : LogCoordinates d := fun _ => Real.log θ-L
  let b : LogCoordinates d := fun _ => Real.log θ
  have H (s : Fin (d+1) → SignTypeˣ) :
      (∫⁻ u : LogCoordinates d, boxIndicator (fun _ => 0) θ
        (Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
          (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)))) ≤ ENNReal.ofReal (L^d) := by
    calc
      _ ≤ ∫⁻ u : LogCoordinates d, (Set.Icc a b).indicator (fun _ => (1:ℝ≥0∞)) u := by
        apply lintegral_mono
        intro u
        by_cases hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
            (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈ coordinateBox (fun _ => 0) θ
        · have hab : u ∈ Set.Icc a b := cube_fiber_log_rectangle hθ hz s u hu
          simp only [boxIndicator,Set.indicator_of_mem hu,Set.indicator_of_mem hab,le_refl]
        · simp only [boxIndicator,Set.indicator_of_notMem hu]
          exact bot_le
      _ = volume (Set.Icc a b) := by rw [lintegral_indicator measurableSet_Icc]; simp
      _ = ∏ i : Fin d, ENNReal.ofReal (b i-a i) := Real.volume_Icc_pi
      _ = ENNReal.ofReal (L^d) := by simp [a,b,← ENNReal.ofReal_pow hL]
  unfold productFiberIntegral
  exact (Finset.sum_le_sum (fun s _ => H s)).trans_eq (by simp [nsmul_eq_mul,L])

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealNorms
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

lemma nonzeroIdeal_absNorm_one_le {K : Type*} [Field K] [NumberField K]
    (I : {J : Ideal (𝓞 K) // J ≠ ⊥}) : (1:ℝ) ≤ Ideal.absNorm I.1 := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp I.2)

lemma normBoundedIdeals_weight_sum_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (X t : ℝ) :
    (∑ I ∈ (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ t),
      globalIdealWeight M (nonzeroIntegralIdealUnit I)) ≤ weightedIdealRealInterval M t t := by
  calc
    _ = ∑ I ∈ (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ t),
        if t-t < (Ideal.absNorm I.1:ℝ) ∧ (Ideal.absNorm I.1:ℝ) ≤ t
        then globalIdealWeight M (nonzeroIntegralIdealUnit I) else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [ite_eq_left ⟨by linarith [nonzeroIdeal_absNorm_one_le I],(Finset.mem_filter.mp hI).2⟩]
    _ ≤ _ := ENNReal.sum_le_tsum _

 

theorem packetMeasure_cube_moment_le_log_sum {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) {θ : ℝ} (hθ : 0 < θ) :
    let X := θ^(d+1)*packetScale M
    (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) *
      ENNReal.ofReal (∑ I ∈ normBoundedIdeals K X,
        (globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal *
          (Real.log (X/(Ideal.absNorm I.1:ℝ)))^d) := by
  dsimp only
  let X := θ^(d+1)*packetScale M
  have hQ := packetScale_pos M
  have hX : 0 < X := mul_pos (pow_pos hθ _) hQ
  rw [packetMeasure_siegel_unfolding M σ hn hodd _ (measurable_boxIndicator _ θ),mul_assoc]
  apply _root_.mul_le_mul_right _ _
  have hfinite : (∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥}, nonzeroIdealWeight M I *
      productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ)
        ((Ideal.absNorm I.1:ℝ)/packetScale M)) =
      ∑ I ∈ normBoundedIdeals K X, nonzeroIdealWeight M I *
        productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ)
          ((Ideal.absNorm I.1:ℝ)/packetScale M) := by
    apply tsum_eq_sum
    intro I hI
    have hN := nonzeroIdeal_absNorm_one_le I
    have hout : θ^(d+1) < (Ideal.absNorm I.1:ℝ)/packetScale M :=
      (lt_div_iff₀ hQ).mpr (lt_of_not_ge (fun H => hI ((mem_normBoundedIdeals K X I).mpr H)))
    rw [productFiberIntegral_cube_eq_zero (by positivity) hout,mul_zero]
  rw [hfinite]
  calc
    _ ≤ ∑ I ∈ normBoundedIdeals K X,
        (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) *
          ENNReal.ofReal ((globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal *
            (Real.log (X/(Ideal.absNorm I.1:ℝ)))^d) := by
      apply Finset.sum_le_sum
      intro I hI
      have hN : (0:ℝ) < Ideal.absNorm I.1 := lt_of_lt_of_le zero_lt_one (nonzeroIdeal_absNorm_one_le I)
      have hNI : (Ideal.absNorm I.1:ℝ)/packetScale M ≤ θ^(d+1) :=
        (div_le_iff₀ hQ).mpr ((mem_normBoundedIdeals K X I).mp hI)
      have H := productFiberIntegral_cube_le hθ (div_pos hN hQ) hNI
      have hlog : θ^(d+1)/((Ideal.absNorm I.1:ℝ)/packetScale M) = X/(Ideal.absNorm I.1:ℝ) := by
        dsimp [X]
        rw [div_div_eq_mul_div]
      rw [hlog] at H
      calc
        _ ≤ nonzeroIdealWeight M I * _ := mul_le_mul_right H _
        _ = _ := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (globalIdealWeight_le_one M _)),
            nonzeroIdealWeight_eq_global]
          ring
    _ = _ := by
      rw [← Finset.mul_sum,← ENNReal.ofReal_sum_of_nonneg]
      intro I hI
      apply mul_nonneg ENNReal.toReal_nonneg
      apply pow_nonneg
      apply Real.log_nonneg
      exact (one_le_div (lt_of_lt_of_le zero_lt_one (nonzeroIdeal_absNorm_one_le I))).mpr
        ((mem_normBoundedIdeals K X I).mp hI)

 

theorem weightedIdeal_log_sum_cutoff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (d : ℕ) (X U Q A : ℝ) (hX : 0 < X) (hU : 0 ≤ U)
    (hA : 0 ≤ A) (hQ : 1 ≤ Q) (hXQ : X ≤ Q) (hUQ : U ≤ Q)
    (hcount : ∀ t : ℝ, U ≤ t → t ≤ Q → weightedIdealRealInterval M t t ≤ ENNReal.ofReal (A*t)) :
    (∑ I ∈ normBoundedIdeals K X,
      (globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal *
        (Real.log (X/(Ideal.absNorm I.1:ℝ)))^d) ≤
      A*U*(Real.log Q)^d + A*X*logMomentConstant d := by
  apply log_weighted_sum_cutoff _ (fun I => (Ideal.absNorm I.1:ℝ))
    (fun I => (globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal) d X U Q A hX hA hQ hXQ
  · exact fun _ _ => ENNReal.toReal_nonneg
  · intro I hI
    exact ⟨nonzeroIdeal_absNorm_one_le I,(mem_normBoundedIdeals K X I).mp hI⟩
  · intro t ht
    have he : (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ t) =
        (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ min t Q) := by
      ext I
      simp only [Finset.mem_filter,le_min_iff]
      constructor
      · rintro ⟨hI,hIt⟩
        exact ⟨hI,hIt,((mem_normBoundedIdeals K X I).mp hI).trans hXQ⟩
      · exact fun h => ⟨h.1,h.2.1⟩
    have H := (normBoundedIdeals_weight_sum_le M X (min t Q)).trans
      ((hcount (min t Q) (le_min ht hUQ) (min_le_right _ _)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) hA)))
    rw [he]
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA (hU.trans ht))).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    simpa only [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (globalIdealWeight_le_one M _))] using H

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma cutoff_ratio_rpow {Q : ℝ} (hQ : 0 < Q) :
    Q^(3/4:ℝ)/Q = (Q^(1/4:ℝ))⁻¹ := by
  calc
    _ = Q^((3/4:ℝ)-1) := by rw [Real.rpow_sub hQ,Real.rpow_one]
    _ = Q^(-(1/4:ℝ)) := by congr 1; norm_num
    _ = _ := Real.rpow_neg hQ.le _

 

theorem packetMeasure_cube_moment_of_count {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) {θ C : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (hQ : 1 ≤ packetScale M)
    (hcount : ∀ t : ℝ, (packetScale M)^(3/4:ℝ) ≤ t → t ≤ packetScale M →
      weightedIdealRealInterval M t t ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (C*t*NumberField.dedekindZeta_residue K)) :
    (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
      ENNReal.ofReal ((Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*C*
        ((Real.log (packetScale M))^d/(packetScale M)^(1/4:ℝ) +
          θ^(d+1)*logMomentConstant d)) := by
  let Q := packetScale M
  let q : ℝ := saturationIndex M
  let κ := NumberField.dedekindZeta_residue K
  let U := Q^(3/4:ℝ)
  let X := θ^(d+1)*Q
  let A := C*κ/q
  let B := C*(U/Q*(Real.log Q)^d+θ^(d+1)*logMomentConstant d)
  have hQ0 : 0 < Q := packetScale_pos M
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M)
  have hk : 0 < κ := NumberField.dedekindZeta_residue_pos K
  have hU : 0 ≤ U := Real.rpow_nonneg hQ0.le _
  have hX : 0 < X := mul_pos (pow_pos hθ _) hQ0
  have hXQ : X ≤ Q := mul_le_of_le_one_left hQ0.le (pow_le_one₀ hθ.le hθ1)
  have hUQ : U ≤ Q := Real.rpow_le_self_of_one_le hQ (by norm_num)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hC hk.le) hq.le
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hC (add_nonneg (mul_nonneg (div_nonneg hU hQ0.le)
      (pow_nonneg (Real.log_nonneg hQ) _)) (mul_nonneg (pow_nonneg hθ.le _)
        (logMomentConstant_nonneg d)))
  have hcount' (t : ℝ) (ht : U ≤ t) (htQ : t ≤ Q) :
      weightedIdealRealInterval M t t ≤ ENNReal.ofReal (A*t) := by
    apply (hcount t ht htQ).trans_eq
    have he : A*t = (C*t*κ)/q := by dsimp [A] <;> ring
    rw [he,ENNReal.ofReal_div_of_pos hq,div_eq_mul_inv]
    simp only [q,κ,ENNReal.ofReal_natCast]
    exact mul_comm _ _
  have H := weightedIdeal_log_sum_cutoff M d X U Q A hX hU hA hQ hXQ hUQ hcount'
  have Hm := packetMeasure_cube_moment_le_log_sum M σ hn hodd hθ
  dsimp only at Hm
  apply Hm.trans
  calc
    _ ≤ (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) * ENNReal.ofReal κ)⁻¹ *
        (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ≥0∞) *
          ENNReal.ofReal (A*U*(Real.log Q)^d+A*X*logMomentConstant d) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal H) _
    _ = (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) * ENNReal.ofReal κ)⁻¹ *
        (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ≥0∞) * (saturationIndex M:ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (B*Q*κ) := by
      have he : A*U*(Real.log Q)^d+A*X*logMomentConstant d = (B*Q*κ)/q := by
        dsimp [A,B,X]
        field_simp
      rw [he,ENNReal.ofReal_div_of_pos hq,div_eq_mul_inv]
      simp only [q,ENNReal.ofReal_natCast]
      ring
    _ = (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ≥0∞)*ENNReal.ofReal B :=
      packet_moment_normalization M _ B hB
    _ = _ := by
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      dsimp only [B,U]
      rw [cutoff_ratio_rpow hQ0]
      dsimp only [Q]
      ring



end PrimeDegreePackets


open MeasureTheory Filter Set Module TopologicalSpace
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.EliminationChain.remainingWordHomeomorph_apply _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.EmbeddingOrder.toRealOrder_apply _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.DukePrimeDegree.InitialRootStep.nextGroupCast_val _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one _root_.OAI.DukePrimeDegree.upperRootWordHomeomorph_apply _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.orbitQuotientMap_mk _root_.infinitePlace_mult_smul
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

 

theorem fieldDiscriminant_le_packetScale_sq {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (M : FullLattice n K) :
    |(NumberField.discr K : ℝ)| ≤ (packetScale M)^2 := by
  have hq : (1:ℝ) ≤ saturationIndex M := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (saturationIndex_ne_zero M)
  have hD := abs_nonneg (NumberField.discr K : ℝ)
  have hs : Real.sqrt |(NumberField.discr K : ℝ)| ≤ packetScale M := by
    unfold packetScale
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hq
  have H := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  simpa only [Real.sq_sqrt hD] using H



open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators


theorem packet_cube_moment_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → packetScale M = Q →
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
          (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*(θ^(d+1)+(Real.log Q)^d/Q^(1/4:ℝ))) := by
  obtain ⟨R,hR,HR⟩ := Hscale
  obtain ⟨C,hC,Hcount⟩ := weightedIdeal_realInterval_of_zeta_scale (d+1) (by omega) hR HR
  let s : ℝ := Fintype.card (Fin (d+1) → SignTypeˣ)
  let B := s*C*(logMomentConstant d+1)
  have hs : 0 < s := by dsimp [s] <;> positivity
  have hL := logMomentConstant_nonneg d
  have hB : 0 < B := by dsimp [B] <;> positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [Hcount 1 le_rfl 1 zero_lt_one,eventually_ge_atTop (1:ℝ)] with Q hcount hQ
  intro K _ _ _ M σ hn hMQ θ hθ hθ1
  have hQ' : 1 ≤ packetScale M := hMQ ▸ hQ
  have H := packetMeasure_cube_moment_of_count M σ hn hodd hθ hθ1 hC.le hQ' (by
    intro t ht htQ
    apply hcount K M (σ 0) hn (hMQ ▸ fieldDiscriminant_le_packetScale_sq M) (by rw [← hMQ]; exact saturationIndex_le_packetScale M) t t
    · simpa only [hMQ] using ht
    · simpa only [one_mul,hMQ] using htQ
    · simp
    · rfl)
  apply H.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hMQ]
  have he : 0 ≤ (Real.log Q)^d/Q^(1/4:ℝ) :=
    div_nonneg (pow_nonneg (Real.log_nonneg hQ) _) (Real.rpow_nonneg (by linarith) _)
  have hθn := pow_nonneg hθ.le (d+1)
  dsimp only [B,s]
  nlinarith [mul_nonneg (mul_nonneg hs.le hC.le) (mul_nonneg hL he)]


theorem packet_tight_of_zeta_scale_oai (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop) :
    IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  obtain ⟨B,hB,Hcube⟩ := packet_cube_moment_of_zeta_scale d hodd Hscale
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨∅,isCompact_empty,fun _ _ => by simp [hεtop]⟩
  let e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  let θ := min (1/2:ℝ) (e/(4*B))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos he (by positivity))
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθe : B*θ^(d+1) ≤ e/4 := by
    have hpow : θ^(d+1) ≤ θ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hθ.le (pow_le_one₀ hθ.le hθ1)
    have he' := (le_div_iff₀ (show 0 < 4*B by positivity)).mp (min_le_right (1/2:ℝ) (e/(4*B)))
    dsimp only [θ] at hpow ⊢
    nlinarith
  have Herror := ((cusp_log_error_vanishes d).comp hQ).eventually_lt_const
    (show (0:ℝ) < e/(4*B) by positivity)
  have Hmass : ∀ᶠ i in atTop,
      packetMeasure (M i) (σ i) (thickLattices (d+1) θ)ᶜ ≤ ε := by
    filter_upwards [hQ.eventually Hcube,Herror] with i hi herror
    apply (cusp_mass_le_cube_moment (packetMeasure (M i) (σ i)) θ).trans
    apply (hi (K i) (M i) (σ i) (hn i) rfl θ hθ hθ1).trans
    rw [← ENNReal.ofReal_toReal hεtop]
    apply ENNReal.ofReal_le_ofReal
    have H := (lt_div_iff₀ (show 0 < 4*B by positivity)).mp herror
    dsimp only [Function.comp_apply] at H
    change B*(θ^(d+1)+(Real.log (packetScale (M i)))^d/(packetScale (M i))^(1/4:ℝ)) ≤ e
    nlinarith
  obtain ⟨i₀,Hi⟩ := eventually_atTop.mp Hmass
  let F : Set (X (d+1)) := ⋃ i : Fin i₀, packetSupport (M i) (σ i)
  have hF : IsCompact F := isCompact_iUnion fun i : Fin i₀ =>
    packetSupport_isCompact (M i) (σ i) (hn i) hodd
  refine ⟨thickLattices (d+1) θ ∪ F,(mahler_compact d θ hθ).union hF,?_⟩
  rintro μ ⟨i,rfl⟩
  by_cases hi : i₀ ≤ i
  · exact (measure_mono (Set.compl_subset_compl.mpr Set.subset_union_left)).trans (Hi i hi)
  · have hs : packetSupport (M i) (σ i) ⊆ thickLattices (d+1) θ ∪ F := by
      intro x hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,Nat.lt_of_not_ge hi⟩,hx⟩)
    apply (measure_mono (Set.compl_subset_compl.mpr hs)).trans
    rw [packetMeasure_compl_support (M i) (σ i) (hn i) hodd]
    exact bot_le


end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.PrimeDegreePackets.packet_tight_of_zeta_scale_oai.{u} := @OAI.PrimeDegreePackets.packet_tight_of_zeta_scale_oai.{u}
