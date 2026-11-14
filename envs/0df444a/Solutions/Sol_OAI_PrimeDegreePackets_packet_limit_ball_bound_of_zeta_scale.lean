-- Prove2me | solution 1 for OAI.PrimeDegreePackets.packet_limit_ball_bound_of_zeta_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:43.329208+00:00
-- url     : https://prove2.me/submissions/6bebabf9-8e09-4c92-9ca4-19b832ca5322

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_packetMeasure_lintegral_signedLogAverage
import Theorems.Thm_OAI_PrimeDegreePackets_signedLabel_siegelTransform_lintegral
import Theorems.Thm_OAI_PrimeDegreePackets_weightedIdeal_realInterval_of_zeta_scale

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

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_ZetaResidues
attribute [-instance] _root_.CyclicCohomology.permutationSublattice_discreteTopology _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.coordinateLattice_discrete _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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



lemma fieldDiscriminant_one_le (K : Type*) [Field K] [NumberField K] :
    1 ≤ |(NumberField.discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

lemma packetScale_pos {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : 0 < packetScale M := by
  unfold packetScale
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M))
    (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (fieldDiscriminant_one_le K)))



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

lemma abs_prod_sub_prod_bound {ι : Type*} (s : Finset ι) (v w : ι → ℝ)
    {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 ≤ ε)
    (hv : ∀ i ∈ s, |v i| ≤ B) (hw : ∀ i ∈ s, |w i| ≤ B)
    (hd : ∀ i ∈ s, |v i-w i| ≤ ε) :
    |∏ i ∈ s, v i - ∏ i ∈ s, w i| ≤ (s.card:ℝ)*ε*B^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hv' : ∀ i ∈ s, |v i| ≤ B := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have hw' : ∀ i ∈ s, |w i| ≤ B := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, |v i-w i| ≤ ε := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hi := ih hv' hw' hd'
    have hp : |∏ i ∈ s, w i| ≤ B^s.card := by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _) hw').trans_eq (by simp)
    simp only [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    calc
      |v a * ∏ i ∈ s, v i - w a * ∏ i ∈ s, w i| =
          |v a * ((∏ i ∈ s, v i)-(∏ i ∈ s, w i)) + (v a-w a)*(∏ i ∈ s,w i)| := by ring_nf
      _ ≤ |v a| *|((∏ i ∈ s, v i)-(∏ i ∈ s, w i))| + |v a-w a| *|∏ i ∈ s,w i| := by
        simpa only [abs_mul] using abs_add_le (v a * ((∏ i ∈ s,v i)-(∏ i ∈ s,w i)))
          ((v a-w a)*(∏ i ∈ s,w i))
      _ ≤ B*((s.card:ℝ)*ε*B^s.card)+ε*B^s.card := by
        exact add_le_add (mul_le_mul (hv a (Finset.mem_insert_self _ _)) hi
          (abs_nonneg _) (by linarith))
          (mul_le_mul (hd a (Finset.mem_insert_self _ _)) hp (abs_nonneg _) hε)
      _ ≤ ((s.card:ℝ)+1)*ε*B^(s.card+1) := by
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right hB (mul_nonneg hε (pow_nonneg (show 0 ≤ B by linarith) s.card))]

lemma log_interval_width_bound {a c ε : ℝ} (hc : 0 < c) (ha : c ≤ a)
    (hε : 0 ≤ ε) (hεc : ε ≤ c/2) :
    Real.log (a+ε)-Real.log (a-ε) ≤ 4*ε/c := by
  have hlo : 0 < a-ε := by linarith
  have hhi : 0 < a+ε := by linarith
  rw [← Real.log_div hhi.ne' hlo.ne']
  have H := Real.log_le_sub_one_of_pos (div_pos hhi hlo)
  apply H.trans
  have he : (a+ε)/(a-ε)-1 = 2*ε/(a-ε) := by field_simp <;> ring
  rw [he]
  apply (div_le_div_iff₀ hlo hc).mpr
  nlinarith

lemma fiberPoint_abs_prod {d : ℕ} (w : Fin (d+1) → SignTypeˣ) (z : ℝ)
    (u : LogCoordinates d) :
    (∏ i, |(Fin.snoc (fun i => signValue (w i.castSucc)*Real.exp (u i))
      (signValue (w (Fin.last d))*z*Real.exp (-∑ i, u i))) i|) = |z| := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,abs_mul,signValue_abs,one_mul,
    abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_sum,← mul_assoc, mul_comm (Real.exp (∑ i, u i)) |z|,
    mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

 

theorem productFiberIntegral_box_le {d : ℕ} (w : Fin (d+1) → ℝ) {c ε : ℝ}
    (hc : 0 < c) (hw : ∀ i, c ≤ |w i|) (hε : 0 ≤ ε) (hεc : ε ≤ c/2) (z : ℝ) :
    productFiberIntegral (boxIndicator w ε) z ≤
      (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d) := by
  let a : LogCoordinates d := fun i => Real.log (|w i.castSucc|-ε)
  let b : LogCoordinates d := fun i => Real.log (|w i.castSucc|+ε)
  have H (s : Fin (d+1) → SignTypeˣ) :
      (∫⁻ u : LogCoordinates d, boxIndicator w ε
        (Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
          (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)))) ≤ ENNReal.ofReal ((4*ε/c)^d) := by
    calc
      _ ≤ ∫⁻ u : LogCoordinates d, (Set.Icc a b).indicator (fun _ => (1:ℝ≥0∞)) u := by
        apply lintegral_mono
        intro u
        by_cases hu : Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
            (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i)) ∈ coordinateBox w ε
        · have hab : u ∈ Set.Icc a b := by
            constructor <;> intro i
            all_goals
              have hv := hu i.castSucc
              simp only [Fin.snoc_castSucc] at hv
              have he : |signValue (s i.castSucc)*Real.exp (u i)| = Real.exp (u i) := by
                rw [abs_mul,signValue_abs,one_mul,abs_of_pos (Real.exp_pos _)]
              have hlo : |w i.castSucc|-ε ≤ Real.exp (u i) := by
                have := abs_sub_abs_le_abs_sub (w i.castSucc) (signValue (s i.castSucc)*Real.exp (u i))
                rw [abs_sub_comm,he] at this
                linarith
              have hhi : Real.exp (u i) ≤ |w i.castSucc|+ε := by
                have := abs_sub_abs_le_abs_sub (signValue (s i.castSucc)*Real.exp (u i)) (w i.castSucc)
                rw [he] at this
                linarith
            · exact (Real.log_le_iff_le_exp (by have := hw i.castSucc; linarith)).mpr hlo
            · exact (Real.le_log_iff_exp_le (by have := hw i.castSucc; linarith)).mpr hhi
          simp only [boxIndicator,Set.indicator_of_mem hu,Set.indicator_of_mem hab,le_refl]
        · simp only [boxIndicator,Set.indicator_of_notMem hu]
          exact bot_le
      _ = volume (Set.Icc a b) := by rw [lintegral_indicator measurableSet_Icc]; simp
      _ = ∏ i : Fin d, ENNReal.ofReal (b i-a i) := Real.volume_Icc_pi
      _ ≤ ∏ _i : Fin d, ENNReal.ofReal (4*ε/c) := by
        apply Finset.prod_le_prod' (fun i _ => ENNReal.ofReal_le_ofReal ?_)
        exact log_interval_width_bound hc (hw i.castSucc) hε hεc
      _ = _ := by simp [← ENNReal.ofReal_pow (by positivity : 0 ≤ 4*ε/c)]
  unfold productFiberIntegral
  exact (Finset.sum_le_sum (fun s _ => H s)).trans_eq (by simp [nsmul_eq_mul])

lemma coordinateBox_product_bound {n : ℕ} {w v : Fin n → ℝ} {b ε : ℝ}
    (hb : 0 ≤ b) (hw : ∀ i, |w i| ≤ b) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hv : v ∈ coordinateBox w ε) :
    |(∏ i, |v i|) - (∏ i, |w i|)| ≤ (n:ℝ)*(b+1)^n*ε := by
  have hd (i : Fin n) : abs (abs (v i) - abs (w i)) ≤ ε := by
    apply abs_le.mpr
    constructor
    · have H := abs_sub_abs_le_abs_sub (w i) (v i)
      rw [abs_sub_comm] at H
      have := hv i
      linarith
    · exact (abs_sub_abs_le_abs_sub (v i) (w i)).trans (hv i)
  have hv' (i : Fin n) : |v i| ≤ b+1 := by
    have H := abs_sub_abs_le_abs_sub (v i) (w i)
    have := hv i
    have := hw i
    linarith
  have H := abs_prod_sub_prod_bound Finset.univ (fun i => |v i|) (fun i => |w i|)
    (show 1 ≤ b+1 by linarith) hε
    (fun i _ => by simpa only [abs_abs] using hv' i)
    (fun i _ => by simpa only [abs_abs] using (hw i).trans (by linarith : b ≤ b+1))
    (fun i _ => hd i)
  simpa only [Finset.card_univ,Fintype.card_fin,mul_right_comm] using H

 

theorem productFiberIntegral_box_supported {d : ℕ} (w : Fin (d+1) → ℝ)
    {c b ε z : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (hwlo : ∀ i, c ≤ |w i|) (hwhi : ∀ i, |w i| ≤ b)
    (hε : 0 ≤ ε) (hεc : ε ≤ c/2) (hε1 : ε ≤ 1) (hz : 0 < z) :
    productFiberIntegral (boxIndicator w ε) z ≤
      if |z-(∏ i, |w i|)| ≤ ((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε then
        (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d)
      else 0 := by
  classical
  split_ifs with ht
  · exact productFiberIntegral_box_le w hc hwlo hε hεc z
  · have Hzero (s : Fin (d+1) → SignTypeˣ) (u : LogCoordinates d) :
        boxIndicator w ε
          (Fin.snoc (fun i => signValue (s i.castSucc)*Real.exp (u i))
            (signValue (s (Fin.last d))*z*Real.exp (-∑ i, u i))) = 0 := by
      apply Set.indicator_of_notMem
      intro hu
      have H := coordinateBox_product_bound hb hwhi hε hε1 hu
      rw [fiberPoint_abs_prod,abs_of_pos hz] at H
      exact ht H
    simp only [productFiberIntegral,Hzero,lintegral_zero,Finset.sum_const_zero,le_refl]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

 

theorem packetMeasure_box_moment_le_count {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (w : Fin (d+1) → ℝ) {b c ε : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) (hwlo : ∀ i, c ≤ |w i|) (hwhi : ∀ i, |w i| ≤ b)
    (hε : 0 < ε) (hεc : ε ≤ c/2) (hε1 : ε ≤ 1) :
    let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
    let z₀ : ℝ := ∏ i, |w i|
    (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      ((Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d)) *
      weightedIdealRealInterval M ((z₀+2*C*ε)*packetScale M) (4*C*ε*packetScale M) := by
  dsimp only
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  let z₀ : ℝ := ∏ i, |w i|
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hQ := packetScale_pos M
  rw [packetMeasure_siegel_unfolding M σ hn hodd _ (measurable_boxIndicator w ε)]
  rw [mul_assoc]
  apply _root_.mul_le_mul_right _ _
  unfold weightedIdealRealInterval
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro I
  have hN : 0 < (Ideal.absNorm I.1:ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2))
  have hz := div_pos hN hQ
  have H := productFiberIntegral_box_supported w hc hb hwlo hwhi hε.le hεc hε1 hz
  change productFiberIntegral (boxIndicator w ε) _ ≤
    if |(Ideal.absNorm I.1:ℝ)/packetScale M-z₀| ≤ C*ε then _ else 0 at H
  rw [nonzeroIdealWeight_eq_global]
  by_cases hs : |(Ideal.absNorm I.1:ℝ)/packetScale M-z₀| ≤ C*ε
  · have hh := abs_le.mp hs
    have hni : (z₀+2*C*ε)*packetScale M-4*C*ε*packetScale M < (Ideal.absNorm I.1:ℝ) ∧
        (Ideal.absNorm I.1:ℝ) ≤ (z₀+2*C*ε)*packetScale M := by
      have hlow : z₀-2*C*ε < (Ideal.absNorm I.1:ℝ)/packetScale M := by
        nlinarith [mul_pos hC hε]
      have hhigh : (Ideal.absNorm I.1:ℝ)/packetScale M ≤ z₀+2*C*ε := by
        nlinarith [mul_pos hC hε]
      constructor
      · have halg : (z₀+2*C*ε)*packetScale M-4*C*ε*packetScale M =
            (z₀-2*C*ε)*packetScale M := by ring
        rw [halg]
        exact (lt_div_iff₀ hQ).mp hlow
      · exact (div_le_iff₀ hQ).mp hhigh
    rw [ite_eq_left hni,mul_comm _ (globalIdealWeight M _)]
    apply _root_.mul_le_mul_right _ _
    simpa only [ite_eq_left hs] using H
  · have Hz : productFiberIntegral (boxIndicator w ε)
        ((Ideal.absNorm I.1:ℝ)/packetScale M) = 0 := by
      apply le_antisymm _ bot_le
      simpa only [ite_eq_right hs,ENNReal.bot_eq_zero] using H
    rw [Hz,mul_zero]
    exact bot_le

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
namespace PrimeDegreePackets

 

theorem box_interval_parameters {n : ℕ} (hn : 0 < n) {b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) :
    let C : ℝ := n*(b+1)^n
    let A₀ : ℝ := b^n+2*C+1
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      r ≤ c/2 ∧ r ≤ 1 ∧ 1 ≤ A₀ ∧ 0 < 4*C*r/A₀ ∧
      ∀ᶠ Q : ℝ in atTop, 0 < Q ∧
        ∀ w : Fin n → ℝ, (∀ i, c ≤ |w i|) → (∀ i, |w i| ≤ b) →
          let z₀ := ∏ i, |w i|
          Q^(3/4:ℝ) ≤ (z₀+2*C*r)*Q ∧
          (z₀+2*C*r)*Q ≤ A₀*Q ∧
          (4*C*r/A₀)*((z₀+2*C*r)*Q) ≤ 4*C*r*Q ∧
          4*C*r*Q ≤ (z₀+2*C*r)*Q := by
  dsimp only
  let C : ℝ := n*(b+1)^n
  let A₀ : ℝ := b^n+2*C+1
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hA : 1 ≤ A₀ := by
    have hbpow := pow_nonneg hb n
    dsimp only [A₀]
    linarith
  have hA0 : 0 < A₀ := by linarith
  refine ⟨min (c/2) (min 1 (c^n/(4*C))), by positivity, ?_⟩
  intro r hr hrr
  have hrc : r ≤ c/2 := (lt_min_iff.mp hrr).1.le
  have hr1 : r ≤ 1 := (lt_min_iff.mp (lt_min_iff.mp hrr).2).1.le
  have hrC : r < c^n/(4*C) := (lt_min_iff.mp (lt_min_iff.mp hrr).2).2
  have hCr : 4*C*r < c^n := by nlinarith [(lt_div_iff₀ (by positivity : 0 < 4*C)).mp hrC]
  refine ⟨hrc,hr1,hA,by positivity,?_⟩
  have Hratio : Tendsto (fun Q : ℝ => Q^(-1/4:ℝ)) atTop (𝓝 0) :=
    by simpa only [neg_div] using (tendsto_rpow_neg_atTop (y := (1/4:ℝ)) (by norm_num))
  filter_upwards [eventually_gt_atTop (0:ℝ),
    Hratio.eventually_lt_const (pow_pos hc n)] with Q hQ hQr
  refine ⟨hQ,?_⟩
  intro w hwlo hwhi
  let z₀ : ℝ := ∏ i, |w i|
  have hzlo : c^n ≤ z₀ := by
    have H := Finset.prod_le_prod (fun (_ : Fin n) (_ : _ ∈ Finset.univ) => hc.le)
      (fun i (_ : i ∈ Finset.univ) => hwlo i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using H
  have hzhi : z₀ ≤ b^n := by
    have H := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => abs_nonneg (w i))
      (fun i (_ : i ∈ Finset.univ) => hwhi i)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using H
  have hsmall : Q^(3/4:ℝ) ≤ c^n*Q := by
    have He : Q^(3/4:ℝ) = Q^(-1/4:ℝ)*Q := by
      calc
        _ = Q^((-1/4:ℝ)+1) := by norm_num
        _ = _ := by rw [Real.rpow_add hQ,Real.rpow_one]
    rw [He]
    exact mul_le_mul_of_nonneg_right hQr.le hQ.le
  have hx : z₀+2*C*r ≤ A₀ := by dsimp only [A₀] <;> nlinarith
  refine ⟨?_,mul_le_mul_of_nonneg_right hx hQ.le,?_,?_⟩
  · exact hsmall.trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hC hr]) hQ.le)
  · have H := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 4*C*r/A₀)
    rw [div_mul_cancel₀ _ hA0.ne'] at H
    simpa only [C,A₀,z₀,mul_assoc] using mul_le_mul_of_nonneg_right H hQ.le
  · exact mul_le_mul_of_nonneg_right (by nlinarith) hQ.le

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma packet_box_constant_identity (d : ℕ) {c ε A : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) (_hA : 0 ≤ A) :
    (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d) *
      ENNReal.ofReal (A*ε) = ENNReal.ofReal
        ((Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*A*ε^(d+1)) := by
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (by positivity))]
  congr 1
  rw [show 4*ε/c=(4/c)*ε by ring,mul_pow,pow_succ]
  ring

 

theorem packetMeasure_box_moment_of_count {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (w : Fin (d+1) → ℝ) {b c ε A : ℝ}
    (hb : 0 ≤ b) (hc : 0 < c) (hwlo : ∀ i, c ≤ |w i|) (hwhi : ∀ i, |w i| ≤ b)
    (hε : 0 < ε) (hεc : ε ≤ c/2) (hε1 : ε ≤ 1) (hA : 0 ≤ A)
    (hcount : weightedIdealRealInterval M
      (((∏ i, |w i|)+2*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε)*packetScale M)
      (4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (A*(4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M)*
        NumberField.dedekindZeta_residue K)) :
    (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
      ENNReal.ofReal ((Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*
        (A*4*((d+1:ℕ):ℝ)*(b+1)^(d+1))*ε^(d+1)) := by
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  have hC : 0 < C := by dsimp [C] <;> positivity
  have H := packetMeasure_box_moment_le_count M σ hn hodd w hb hc hwlo hwhi hε hεc hε1
  dsimp only at H
  have hcount' : weightedIdealRealInterval M
      (((∏ i, |w i|)+2*C*ε)*packetScale M) (4*C*ε*packetScale M) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ * ENNReal.ofReal
        ((A*4*C*ε)*packetScale M*NumberField.dedekindZeta_residue K) := by
    simpa only [C,mul_assoc] using hcount
  apply H.trans
  calc
    _ ≤ _ := mul_le_mul_right hcount' _
    _ = ((Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) * ENNReal.ofReal ((4*ε/c)^d)) *
        ENNReal.ofReal (A*4*C*ε) := by
      rw [← mul_assoc]
      exact packet_moment_normalization M _ _ (by positivity)
    _ = _ := by
      rw [packet_box_constant_identity d hc hε.le (by positivity)]
      congr 1
      dsimp [C]
      ring



end PrimeDegreePackets

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

lemma right_ball_isOpen {n : ℕ} (x : X n) (r : ℝ) :
    IsOpen ((fun h => rightAction x h) '' matrixBall n r) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change IsOpen ((fun h => Quotient.mk _ (g*h)) '' matrixBall n r)
    rw [← Set.image_image]
    exact (quotient_covering n).isOpenMap _
      ((Homeomorph.mulLeft g).isOpenMap _ (matrixBall_isOpen n r))

 

lemma vecMul_sub_coordinate_le {n : ℕ} (w : Fin n → ℝ) (h : G n)
    {r : ℝ} (hr : h ∈ matrixBall n r) (j : Fin n) :
    |(w ᵥ* h.1) j - w j| ≤ r * ∑ i, |w i| := by
  have he : (w ᵥ* h.1) j - w j =
      ∑ i, w i * (h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) := by
    calc
      _ = (w ᵥ* (h.1 - (1 : Matrix (Fin n) (Fin n) ℝ))) j := by
        rw [Matrix.vecMul_sub, Matrix.vecMul_one]
        rfl
      _ = _ := rfl
  rw [he]
  calc
    _ ≤ ∑ i, |w i * (h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * r := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hr i j).le (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]



lemma continuous_integer_row_coordinate {n : ℕ} (z : Fin n → ℤ) (j : Fin n) :
    Continuous (fun g : G n => ((fun i => (z i : ℝ)) ᵥ* g.1) j) := by
  change Continuous (fun g : G n => ∑ i, (z i : ℝ)*g.1 i j)
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  exact (continuous_apply j).comp ((continuous_apply i).comp
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)

lemma vectorEnvelope_isOpen (n k : ℕ) : IsOpen (vectorEnvelope n k) := by
  have heq : vectorEnvelope n k =
      ⋃ z : Fin n → ℤ,
        Quotient.mk (QuotientGroup.rightRel (integralGroup n)) ''
          {g : G n | ∀ j,
            (1:ℝ)/(k+1) < |((fun i => (z i : ℝ)) ᵥ* g.1) j| ∧
            |((fun i => (z i : ℝ)) ᵥ* g.1) j| < k+1} := by
    ext x
    simp only [vectorEnvelope, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨g,hg,z,hz⟩
      exact ⟨z,g,hz,hg⟩
    · rintro ⟨z,g,hz,hg⟩
      exact ⟨g,hg,z,hz⟩
  rw [heq]
  apply isOpen_iUnion
  intro z
  apply (quotient_covering n).isOpenMap
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_lt continuous_const (continuous_integer_row_coordinate z j).abs).inter
    (isOpen_lt (continuous_integer_row_coordinate z j).abs continuous_const)

lemma vectorEnvelope_mono {n j k : ℕ} (hjk : j ≤ k) :
    vectorEnvelope n j ⊆ vectorEnvelope n k := by
  rintro x ⟨g,hg,z,hz⟩
  refine ⟨g,hg,z,fun i => ?_⟩
  have hjkR : (j:ℝ)+1 ≤ k+1 := by exact_mod_cast Nat.succ_le_succ hjk
  refine ⟨lt_of_le_of_lt ?_ (hz i).1, (hz i).2.trans_le hjkR⟩
  exact one_div_le_one_div_of_le (by positivity) hjkR

lemma mem_vectorEnvelope {n : ℕ} (x : X n) : ∃ k, x ∈ vectorEnvelope n k := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨z,hz⟩ := exists_integer_row_no_zero_coordinate g
    let w : Fin n → ℝ := (fun i => (z i : ℝ)) ᵥ* g.1
    obtain ⟨k,hk⟩ := exists_nat_gt (max ‖w‖ ‖fun j => 1 / |w j|‖)
    refine ⟨k,g,rfl,z,fun j => ?_⟩
    have habs : 0 < |w j| := abs_pos.mpr (hz j)
    have hw : |w j| < k+1 := by
      have H : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
      linarith [le_max_left ‖w‖ ‖fun j => 1 / |w j|‖]
    have hi : 1 / |w j| < k+1 := by
      have H : |1 / (|w j|)| ≤ ‖fun j => 1 / |w j|‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j => 1 / |w j|) j
      rw [abs_of_pos (one_div_pos.mpr habs)] at H
      linarith [le_max_right ‖w‖ ‖fun j => 1 / |w j|‖]
    refine ⟨?_,hw⟩
    apply (div_lt_iff₀ (show (0:ℝ) < k+1 by positivity)).mpr
    have H := (div_lt_iff₀ habs).mp hi
    nlinarith

 

theorem compact_uniform_vector_envelope {n : ℕ} {Ω : Set (X n)} (hΩ : IsCompact Ω) :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧ ∀ x ∈ Ω,
      ∃ g : G n, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g = x ∧
        ∃ z : Fin n → ℤ, ∀ j,
          δ < |((fun i => (z i : ℝ)) ᵥ* g.1) j| ∧
          |((fun i => (z i : ℝ)) ᵥ* g.1) j| < B := by
  obtain ⟨s,hs⟩ := hΩ.elim_finite_subcover (vectorEnvelope n)
    (vectorEnvelope_isOpen n) (by
      intro x _
      obtain ⟨k,hk⟩ := mem_vectorEnvelope x
      exact Set.mem_iUnion.mpr ⟨k,hk⟩)
  let N := ∑ k ∈ s, k
  refine ⟨N+1,1/(N+1),by positivity,by positivity,?_⟩
  intro x hx
  obtain ⟨k,hks,hxk⟩ := Set.mem_iUnion₂.mp (hs hx)
  have hkN : k ≤ N := Finset.single_le_sum (fun i _ => Nat.zero_le i) hks
  exact vectorEnvelope_mono hkN hxk

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
-- module Solutions.OAIQ244_DUKE.PrimePackets_CuspMass
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xStandardBorel _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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



lemma right_ball_indicator_le_siegel {n : ℕ} (g : G n) (z : Fin n → ℤ)
    (hz : z ≠ 0) {r ε : ℝ} (_hr : 0 ≤ r)
    (hε : r*(∑ i, |integerRowMap g.1 z i|) ≤ ε) (y : X n) :
    ((fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r).indicator
      (fun _ => (1:ℝ≥0∞)) y ≤ siegelTransform (boxIndicator (integerRowMap g.1 z) ε) y := by
  let S := (fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r
  by_cases hy : y ∈ S
  · obtain ⟨h,hh,rfl⟩ := hy
    change S.indicator (fun _ => (1:ℝ≥0∞)) (Quotient.mk _ (g*h)) ≤
      siegelTransform (boxIndicator (integerRowMap g.1 z) ε) (Quotient.mk _ (g*h))
    rw [siegelTransform_mk]
    have hv : integerRowMap (g*h).1 z ∈ coordinateBox (integerRowMap g.1 z) ε := by
      intro j
      have H := vecMul_sub_coordinate_le (integerRowMap g.1 z) h hh j
      rw [integerRowMap_apply,integerRowMap_apply,
        Matrix.SpecialLinearGroup.coe_mul,← Matrix.vecMul_vecMul]
      simpa only [integerRowMap_apply] using H.trans hε
    have H := ENNReal.le_tsum (f := fun v : {z : Fin n → ℤ // z ≠ 0} =>
      boxIndicator (integerRowMap g.1 z) ε (integerRowMap (g*h).1 v.1)) ⟨z,hz⟩
    have hyS : Quotient.mk _ (g*h) ∈ S := ⟨h,hh,rfl⟩
    simpa only [boxIndicator,Set.indicator_of_mem hv,Set.indicator_of_mem hyS] using H
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

lemma right_ball_mass_le_box_moment {n : ℕ} (μ : Measure (X n)) (g : G n)
    (z : Fin n → ℤ) (hz : z ≠ 0) {r ε : ℝ} (hr : 0 ≤ r)
    (hε : r*(∑ i, |integerRowMap g.1 z i|) ≤ ε) :
    μ ((fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r) ≤
      ∫⁻ x, siegelTransform (boxIndicator (integerRowMap g.1 z) ε) x ∂μ := by
  calc
    _ = ∫⁻ x, ((fun h => rightAction (Quotient.mk _ g) h) '' matrixBall n r).indicator
        (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_indicator (right_ball_isOpen (Quotient.mk _ g) r).measurableSet]
      simp
    _ ≤ _ := lintegral_mono (right_ball_indicator_le_siegel g z hz hr hε)

 

lemma open_mass_le_of_probability_limit {n : ℕ}
    (μ : ℕ → ProbabilityMeasure (X n)) (ν : ProbabilityMeasure (X n))
    (hlim : Tendsto μ atTop (𝓝 ν)) {S : Set (X n)} (hS : IsOpen S)
    {B : ℝ≥0∞} (hB : ∀ᶠ i in atTop, (μ i : Measure (X n)) S ≤ B) :
    (ν : Measure (X n)) S ≤ B := by
  exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hS).trans
    (liminf_le_of_frequently_le (Filter.Eventually.frequently hB))

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_HaarUniqueness
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

 
theorem packet_box_moment_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ B r₀ : ℝ, 0 < B ∧ 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < r₀ → ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → packetScale M = Q →
        ∀ w : Fin (d+1) → ℝ, (∀ i, c ≤ |w i|) → (∀ i, |w i| ≤ b) →
          (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*ε^(d+1)) := by
  obtain ⟨R,hR,HR⟩ := Hscale
  obtain ⟨A,hA,Hcount⟩ := weightedIdeal_realInterval_of_zeta_scale (d+1) (by omega) hR HR
  obtain ⟨r₀,hr₀,Hpar⟩ := box_interval_parameters (n := d+1) (by omega) hb hc
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  let A₀ : ℝ := b^(d+1)+2*C+1
  let B : ℝ := (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*(A*4*C)
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hB : 0 < B := by dsimp [B] <;> positivity
  refine ⟨B,r₀,hB,hr₀,?_⟩
  intro ε hε hεr
  obtain ⟨hεc,hε1,hA₀,hη,Hε⟩ := Hpar ε hε hεr
  filter_upwards [Hε,Hcount A₀ hA₀ (4*C*ε/A₀) hη] with Q hQ hcount
  intro K _ _ _ M σ hn hscale w hwlo hwhi
  obtain ⟨hxl,hxu,hrel,hyx⟩ := hQ.2 w hwlo hwhi
  have hq : (saturationIndex M:ℝ) ≤ Q := hscale ▸ saturationIndex_le_packetScale M
  have H := hcount K M (σ 0) hn (hscale ▸ fieldDiscriminant_le_packetScale_sq M) hq _ _ hxl hxu hrel hyx
  rw [← hscale] at H
  have H' : weightedIdealRealInterval M
      (((∏ i, |w i|)+2*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε)*packetScale M)
      (4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (A*(4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M)*
        NumberField.dedekindZeta_residue K) := by
    simpa only [C,mul_assoc] using H
  convert packetMeasure_box_moment_of_count M σ hn hodd w hb hc hwlo hwhi hε hεc hε1 hA.le H' using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [B,C]
  congr 1
  ring


theorem packet_ball_bound_of_zeta_scale (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → packetScale M = Q →
        ∀ x ∈ Ω, packetMeasure M σ ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
          ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨b,c,hb,hc,Hvec⟩ := compact_uniform_vector_envelope hΩ
  obtain ⟨A,ε₀,hA,hε₀,Hbox⟩ := packet_box_moment_of_zeta_scale d hodd Hscale hb.le hc
  let E : ℝ := (d+1:ℕ)*b
  have hE : 0 < E := by dsimp [E] <;> positivity
  refine ⟨A*E^(d+1),ε₀/E,by positivity,div_pos hε₀ hE,?_⟩
  intro r hr hrr
  have hrε : E*r < ε₀ := by nlinarith [(lt_div_iff₀ hE).mp hrr]
  filter_upwards [Hbox (E*r) (mul_pos hE hr) hrε] with Q hQ
  intro K _ _ _ M σ hn hMQ x hx
  obtain ⟨g,hg,z,hz⟩ := Hvec x hx
  have hzne : z ≠ 0 := by
    intro he
    have H : c < (0:ℝ) := by simpa [he,Matrix.vecMul,dotProduct] using (hz 0).1
    exact hc.not_gt H
  have hlo (i) : c ≤ |integerRowMap g.1 z i| := by
    simpa only [integerRowMap_apply] using (hz i).1.le
  have hhi (i) : |integerRowMap g.1 z i| ≤ b := by
    simpa only [integerRowMap_apply] using (hz i).2.le
  have hsum : (∑ i, |integerRowMap g.1 z i|) ≤ E := by
    calc
      _ ≤ ∑ _ : Fin (d+1), b := Finset.sum_le_sum fun i _ => hhi i
      _ = E := by simp [E]
  have H := right_ball_mass_le_box_moment (packetMeasure M σ) g z hzne hr.le
    (show r*(∑ i, |integerRowMap g.1 z i|) ≤ E*r by nlinarith)
  rw [hg] at H
  refine H.trans ((hQ K M σ hn hMQ (integerRowMap g.1 z) hlo hhi).trans_eq ?_)
  congr 1
  rw [mul_pow]
  ring

 
theorem packet_limit_ball_bound_of_zeta_scale_oai (d : ℕ) (hodd : Odd (d+1))
    (Hscale : UniformZetaScaleBound.{u} (d+1))
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν))
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → r < r₀ →
      (ν : Measure (X (d+1))) ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
        ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨C,r₀,hC,hr₀,H⟩ := packet_ball_bound_of_zeta_scale d hodd Hscale hΩ
  refine ⟨C,r₀,hC,hr₀,?_⟩
  intro x hx r hr hrr
  apply open_mass_le_of_probability_limit _ ν hlim (right_ball_isOpen x r)
  filter_upwards [hQ.eventually (H r hr hrr)] with i hi
  exact hi (K i) (M i) (σ i) (hn i) rfl x hx


end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.PrimeDegreePackets.packet_limit_ball_bound_of_zeta_scale_oai.{u} := @OAI.PrimeDegreePackets.packet_limit_ball_bound_of_zeta_scale_oai.{u}
