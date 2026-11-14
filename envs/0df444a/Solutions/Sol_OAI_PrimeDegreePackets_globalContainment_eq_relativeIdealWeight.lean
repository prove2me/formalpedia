-- Prove2me | solution 1 for OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:16.486116+00:00
-- url     : https://prove2.me/submissions/2f854f8a-2bb3-48dd-98b6-0c85d3979dd1

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PacketAlgebra
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.model_units_measurableSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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



theorem globalContainmentProbability_eq_prod
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : K)
    (ha : a ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (Nat.card {N : globalLabels M I // a ∈ N.val} : ℝ) / Nat.card (globalLabels M I) =
      ∏ p : labelPrimes M, localContainmentProbability M I p.val
        ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p.val K) a) := by
  rw [Nat.card_congr (globalContainmentEquiv M hn I a ha),Nat.card_pi,globalLabels_card_prod M hn I]
  simp only [Nat.cast_prod,Finset.prod_div_distrib,localContainmentProbability]

open Topology
open scoped Pointwise



theorem isClosed_unit_smul_submodule_eq
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (P Q : Submodule R A) (hP : IsClosed (P : Set A)) (hQ : IsClosed (Q : Set A)) :
    IsClosed {u : Aˣ | (u : A) • P = Q} := by
  have he : {u : Aˣ | (u : A) • P = Q} =
      {u : Aˣ | ∀ x ∈ P, (u : A) * x ∈ Q} ∩
      {u : Aˣ | ∀ x ∈ Q, (↑(u⁻¹) : A) * x ∈ P} := by
    ext u
    constructor
    · intro h
      constructor
      · intro x hx
        rw [← h]
        exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x,hx,rfl⟩
      · intro x hx
        rw [← h] at hx
        obtain ⟨y,hy,hye⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
        change (u : A) * y = x at hye
        rw [← hye,← mul_assoc,Units.inv_mul,one_mul]
        exact hy
    · rintro ⟨h1,h2⟩
      apply le_antisymm
      · intro x hx
        obtain ⟨y,hy,rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
        exact h1 y hy
      · intro x hx
        exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
          ⟨↑(u⁻¹) * x,h2 x hx,by simp [smul_eq_mul,← mul_assoc]⟩
  rw [he]
  simp only [Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    exact hQ.preimage (Units.continuous_val.mul_const x)
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    exact hP.preimage ((Units.continuous_val.comp continuous_inv).mul_const x)

lemma compact_smul_submodule {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [TopologicalSpace A] [IsTopologicalRing A] (a : A)
    (N : Submodule R A) (hN : IsCompact (N : Set A)) : IsCompact (a • N : Set A) := by
  have he : (a • N : Set A) = (fun x : A => a * x) '' (N : Set A) := by
    ext x
    exact Submodule.mem_smul_pointwise_iff_exists _ _ _
  rw [he]
  exact hN.image (continuous_const.mul continuous_id)

lemma normalizedLocalModule_compact {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime] :
    IsCompact (normalizedLocalModule M p : Set (LocalAlgebra p K)) :=
  compact_smul_submodule _ _ (completedLattice_compact M hn p)

open Polynomial



open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module


open MeasureTheory
open scoped ENNReal
 
theorem haar_stabilizer_eq_inv_card {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (x : α) [Finite (MulAction.orbit G x)]
    (hx : MeasurableSet (MulAction.stabilizer G x : Set G)) :
    μ (MulAction.stabilizer G x : Set G) = (Nat.card (MulAction.orbit G x) : ℝ≥0∞)⁻¹ := by
  let : Nonempty (MulAction.orbit G x) := ⟨⟨x,MulAction.mem_orbit_self x⟩⟩
  let e := MulAction.orbitEquivQuotientStabilizer G x
  let : Finite (G ⧸ MulAction.stabilizer G x) := Finite.of_equiv _ e
  let : (MulAction.stabilizer G x).FiniteIndex := ⟨Nat.card_pos.ne'⟩
  have hc : (Nat.card (MulAction.orbit G x) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have he : (MulAction.stabilizer G x).index = Nat.card (MulAction.orbit G x) :=
    (Nat.card_congr e).symm
  rw [← one_div (Nat.card (MulAction.orbit G x) : ℝ≥0∞)]
  apply (ENNReal.eq_div_iff hc (by simp)).mpr
  simpa only [he, measure_univ] using (MulAction.stabilizer G x).index_mul_measure hx μ

 
theorem haar_orbit_fiber {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (x y : α) [Finite (MulAction.orbit G x)]
    (hx : MeasurableSet (MulAction.stabilizer G x : Set G))
    (hy : y ∈ MulAction.orbit G x) :
    μ {g : G | g • x = y} = (Nat.card (MulAction.orbit G x) : ℝ≥0∞)⁻¹ := by
  obtain ⟨a,rfl⟩ := hy
  have he : {g : G | g • x = a • x} =
      (fun g : G => a⁻¹ * g) ⁻¹' (MulAction.stabilizer G x : Set G) := by
    ext g
    change (g • x = a • x) ↔ (a⁻¹ * g) • x = x
    rw [mul_smul,inv_smul_eq_iff]
  rw [he,measure_preimage_mul,haar_stabilizer_eq_inv_card μ x hx]

lemma measurable_orbit_fiber {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (x y : α) (hx : MeasurableSet (MulAction.stabilizer G x : Set G))
    (hy : y ∈ MulAction.orbit G x) : MeasurableSet {g : G | g • x = y} := by
  obtain ⟨a,rfl⟩ := hy
  have he : {g : G | g • x = a • x} =
      (fun g : G => a⁻¹ * g) ⁻¹' (MulAction.stabilizer G x : Set G) := by
    ext g
    change (g • x = a • x) ↔ (a⁻¹ * g) • x = x
    rw [mul_smul,inv_smul_eq_iff]
  rw [he]
  exact hx.preimage (measurable_const_mul _)

 
theorem haar_orbit_subset {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (x : α) [Finite (MulAction.orbit G x)]
    (hx : MeasurableSet (MulAction.stabilizer G x : Set G)) (S : Set α) :
    μ {g : G | g • x ∈ S} =
      (Nat.card {y : MulAction.orbit G x // y.val ∈ S} : ℝ≥0∞) /
        Nat.card (MulAction.orbit G x) := by
  classical
  let β := {y : MulAction.orbit G x // y.val ∈ S}
  let : Fintype β := Fintype.ofFinite β
  have he : {g : G | g • x ∈ S} = ⋃ y : β, {g : G | g • x = y.val.val} := by
    ext g
    constructor
    · intro hg
      exact Set.mem_iUnion.mpr ⟨⟨⟨g • x,⟨g,rfl⟩⟩,hg⟩,rfl⟩
    · intro hg
      obtain ⟨y,hy⟩ := Set.mem_iUnion.mp hg
      change g • x = y.val.val at hy
      change g • x ∈ S
      rw [hy]
      exact y.property
  rw [he,measure_iUnion]
  · simp only [haar_orbit_fiber μ x _ hx (Subtype.property _),tsum_fintype,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,div_eq_mul_inv]
    rfl
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro g ha hb
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    exact ha.symm.trans hb
  · intro y
    exact measurable_orbit_fiber x y.val hx y.val.property


lemma localUnit_smul_base {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] (z : (completedMaximalOrder (K := K) p)ˣ) :
    z • localChoiceBase M I p =
      ((idealLocalGenerator p I : LocalAlgebra p K) *
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K)) • normalizedLocalModule M p := by
  change ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) •
    ((idealLocalGenerator p I : LocalAlgebra p K) • normalizedLocalModule M p) = _
  rw [smul_smul,mul_comm]

lemma localModuleChoices_eq_orbit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (p : ℕ) [Fact p.Prime] :
    MulAction.orbit (completedMaximalOrder (K := K) p)ˣ (localChoiceBase M I p) =
      localModuleChoices M I p := by
  ext N
  simp only [MulAction.mem_orbit_iff,localModuleChoices,Set.mem_range,localUnit_smul_base]

lemma localChoiceStabilizer_measurable {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime] :
    MeasurableSet (MulAction.stabilizer (completedMaximalOrder (K := K) p)ˣ
      (localChoiceBase M I p) : Set (completedMaximalOrder (K := K) p)ˣ) := by
  let N := localChoiceBase M I p
  have hN : IsClosed (N : Set (LocalAlgebra p K)) :=
    (compact_smul_submodule _ _ (normalizedLocalModule_compact M hn p)).isClosed
  let f : completedMaximalOrder (K := K) p →* LocalAlgebra p K :=
    (completedMaximalOrder (K := K) p).val.toMonoidHom
  have hf : Continuous f := continuous_subtype_val
  have h := (isClosed_unit_smul_submodule_eq N N hN hN).preimage
    (Units.continuous_map (f := f) hf)
  exact h.measurableSet



theorem localUnitHaarProbability_containment {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (p : ℕ) [Fact p.Prime] (x : LocalAlgebra p K) :
    localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
      x ∈ ((idealLocalGenerator p I : LocalAlgebra p K) *
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K)) • normalizedLocalModule M p} =
      (Nat.card (localContainmentLabels M I p x) : ℝ≥0∞) / Nat.card (localModuleChoices M I p) := by
  let G := (completedMaximalOrder (K := K) p)ˣ
  let : Finite (MulAction.orbit G (localChoiceBase M I p)) := by
    rw [localModuleChoices_eq_orbit]
    exact (localModuleChoices_finite M hn I p).to_subtype
  have h := haar_orbit_subset (localUnitHaarProbability p) (localChoiceBase M I p)
    (localChoiceStabilizer_measurable M hn I p) {N | x ∈ N}
  have hc : Nat.card {y : MulAction.orbit G (localChoiceBase M I p) // x ∈ y.val} =
      Nat.card (localContainmentLabels M I p x) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.setCongr (localModuleChoices_eq_orbit M I p))
      (fun _ => Iff.rfl)
  simp only [Set.mem_ofPred_eq] at h
  rw [hc] at h
  simpa only [localUnit_smul_base,localModuleChoices_eq_orbit] using h

lemma haar_smul_containment {G A : Type*} [Group G] [MulAction G A]
    [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (L : Set A) (u : G) (x : A) :
    μ {z : G | u • x ∈ z • L} = μ {z : G | x ∈ z • L} := by
  have he : {z : G | u • x ∈ z • L} =
      (fun z : G => u⁻¹ * z) ⁻¹' {z : G | x ∈ z • L} := by
    ext z
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_smul_set_iff_inv_smul_mem,
      mul_inv_rev,inv_inv,mul_smul]
  rw [he,measure_preimage_mul]

 
lemma local_generators_associated {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (u v : (LocalAlgebra p K)ˣ)
    (h : (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule =
      (v : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) :
    ∃ z : (completedMaximalOrder (K := K) p)ˣ,
      (u : LocalAlgebra p K) =
        ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) * v := by
  have hr : ((v⁻¹*u : (LocalAlgebra p K)ˣ) : LocalAlgebra p K) •
      (completedMaximalOrder (K := K) p).toSubmodule =
        (completedMaximalOrder (K := K) p).toSubmodule := by
    rw [Units.val_mul,← smul_smul,h,smul_smul,Units.inv_mul,one_smul]
  obtain ⟨z,hz⟩ := completedMaximalOrder_unit_of_smul_eq p (v⁻¹*u) hr
  refine ⟨z,?_⟩
  rw [hz,Units.val_mul,mul_right_comm,Units.inv_mul,one_mul]

lemma completedFractionalIdeal_generator_mul {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedFractionalIdeal p ((I*J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      ((idealLocalGenerator p I : LocalAlgebra p K) * idealLocalGenerator p J) •
        (completedMaximalOrder (K := K) p).toSubmodule := by
  rw [Units.val_mul,completedFractionalIdeal_mul,idealLocalGenerator_spec,idealLocalGenerator_spec]
  rw [← mul_smul_mul_comm]
  rw [(completedMaximalOrder (K := K) p).isIdempotentElem_toSubmodule.eq]



lemma localIdealWeight_eq_of_generator {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (u : (LocalAlgebra p K)ˣ)
    (hu : completedFractionalIdeal p (J : FractionalIdeal (𝓞 K)⁰ K) =
      (u : LocalAlgebra p K) • (completedMaximalOrder (K := K) p).toSubmodule) :
    localIdealWeight M p J =
      localUnitHaarProbability p {z : (completedMaximalOrder (K := K) p)ˣ |
        (u : LocalAlgebra p K) ∈
          ((z : completedMaximalOrder (K := K) p) : LocalAlgebra p K) • normalizedLocalModule M p} := by
  obtain ⟨v,hv⟩ := local_generators_associated p (idealLocalGenerator p J) u
    ((idealLocalGenerator_spec p J).symm.trans hu)
  unfold localIdealWeight
  rw [hv]
  exact haar_smul_containment (localUnitHaarProbability p)
    (normalizedLocalModule M p : Set (LocalAlgebra p K)) v u


lemma relativeElementIdeal_generator {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    completedFractionalIdeal p (relativeElementIdeal I a : FractionalIdeal (𝓞 K)⁰ K) =
      (((Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom a) *
        (idealLocalGenerator p I)⁻¹ : (LocalAlgebra p K)ˣ) : LocalAlgebra p K) •
          (completedMaximalOrder (K := K) p).toSubmodule := by
  let J := relativeElementIdeal I a
  let i := idealLocalGenerator p I
  let j := idealLocalGenerator p J
  let b := Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom a
  have hJI : J*I = toPrincipalIdeal (𝓞 K) K a := by dsimp [J,relativeElementIdeal] <;> simp
  have h : (j : LocalAlgebra p K) • ((i : LocalAlgebra p K) •
      (completedMaximalOrder (K := K) p).toSubmodule) = (b : LocalAlgebra p K) •
        (completedMaximalOrder (K := K) p).toSubmodule := by
    rw [smul_smul,← completedFractionalIdeal_generator_mul,hJI,coe_toPrincipalIdeal]
    change completedFractionalIdeal p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) =
      (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (a : K) •
        completedFractionalIdeal p 1
    simpa only [mul_one] using completedFractionalIdeal_singleton_mul p 1 (a : K)
  have H := congrArg (fun N : Submodule (PadicInt p) (LocalAlgebra p K) =>
    (↑(i⁻¹) : LocalAlgebra p K) • N) h
  rw [smul_smul,smul_smul,mul_right_comm,Units.inv_mul,one_mul] at H
  rw [idealLocalGenerator_spec]
  change (j : LocalAlgebra p K) • _ = _
  rw [H,smul_smul,mul_comm]
  rfl

 

theorem localContainment_eq_relativeIdealWeight
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (p : ℕ) [Fact p.Prime] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ) :
    (Nat.card (localContainmentLabels M I p
      ((Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K) (a : K))) : ℝ≥0∞) /
        Nat.card (localModuleChoices M I p) = localIdealWeight M p (relativeElementIdeal I a) := by
  rw [← localUnitHaarProbability_containment M hn I p]
  rw [localIdealWeight_eq_of_generator M p _ _ (relativeElementIdeal_generator p I a)]
  congr 1
  ext z
  let b : (LocalAlgebra p K)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : K →ₐ[ℚ] LocalAlgebra p K).toMonoidHom a
  let i := idealLocalGenerator p I
  let R := completedMaximalOrder (K := K) p
  change (b : LocalAlgebra p K) ∈ ((i : LocalAlgebra p K) * ((z : R) : LocalAlgebra p K)) •
      normalizedLocalModule M p ↔
    ((b*i⁻¹ : (LocalAlgebra p K)ˣ) : LocalAlgebra p K) ∈
      ((z : R) : LocalAlgebra p K) • normalizedLocalModule M p
  rw [← smul_smul]
  change (b : LocalAlgebra p K) ∈ i • (((z : R) : LocalAlgebra p K) •
      (normalizedLocalModule M p : Set (LocalAlgebra p K))) ↔ _
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (↑(i⁻¹) : LocalAlgebra p K) * b ∈ _ ↔ _
  rw [Units.val_mul,mul_comm]
  rfl


lemma localIdealWeight_le_one {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (p : ℕ) [Fact p.Prime]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : localIdealWeight M p J ≤ 1 :=
  prob_le_one

lemma globalIdealWeight_le_one {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : globalIdealWeight M J ≤ 1 := by
  apply Finset.prod_le_one'
  intro prime _
  exact localIdealWeight_le_one M prime.val J

 
theorem globalContainment_eq_relativeIdealWeight_oai
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ)
    (ha : (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (Nat.card {N : globalLabels M I // (a : K) ∈ N.val} : ℝ≥0∞) / Nat.card (globalLabels M I) =
      globalIdealWeight M (relativeElementIdeal I a) := by
  have hleft : (Nat.card {N : globalLabels M I // (a : K) ∈ N.val} : ℝ≥0∞) /
      Nat.card (globalLabels M I) ≠ ⊤ := by
    apply ENNReal.div_ne_top (by simp)
    exact_mod_cast (globalLabels_card_pos M hn I).ne'
  have hright : globalIdealWeight M (relativeElementIdeal I a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (globalIdealWeight_le_one M _)
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_natCast,globalIdealWeight,ENNReal.toReal_prod]
  rw [globalContainmentProbability_eq_prod M hn I a ha]
  apply Finset.prod_congr rfl
  intro p _
  have h := congrArg ENNReal.toReal (localContainment_eq_relativeIdealWeight M hn p.val I a)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast,localContainmentProbability] using h

end PrimeDegreePackets
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight_oai.{u_1} := @OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight_oai.{u_1}
