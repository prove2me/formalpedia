-- Prove2me | solution 1 for OAI.PrimeDegreePackets.weightedIdeal_small_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:15.919169+00:00
-- url     : https://prove2.me/submissions/6c8a78b7-58e3-4a01-92ad-a0d77121d02a

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036
import Theorems.Thm_OAI_PrimeDegreePackets_coprime_ideal_scaled_interval

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealCoefficients
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.DiscreteValuationField.finite_nsmulAddKernel_padicInt_pi _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_multiplicative_nthPowerKernel _root_.LocalFieldTheory.finite_nsmulAddKernel_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.primaryIdealMultisetEquiv_val _root_.OAI.PrimeDegreePackets.primaryIdealNormEquiv_val _root_.infinitePlace_mult_smul
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

variable (K : Type*) [Field K] [NumberField K]



lemma idealCoefficient_pos (m : ℕ) (hm : m ≠ 0) :
    idealCoefficient K m = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := by
  simp [idealCoefficient,hm]

lemma idealCoefficient_one : idealCoefficient K 1 = 1 := by
  simp [idealCoefficient, Ideal.absNorm_eq_one_iff]

lemma ideal_factor_count_le {I : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) : (normalizedFactors I).card ≤ r := by
  have hI0 : I ≠ ⊥ := by
    intro h; have H : (0:ℕ) = p^r := by simpa [h] using hI
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have H : p ^ (normalizedFactors I).card ≤ Ideal.absNorm I := by
    have H := Multiset.pow_card_le_prod (s := (normalizedFactors I).map Ideal.absNorm)
      (a := p) (by
        intro x hx
        obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hx
        exact (ideal_factor_prime_power K hp hI hP).2)
    simpa only [Multiset.card_map, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI0] using H
  rw [hI] at H
  exact (pow_le_pow_iff_right₀ hp.one_lt).mp H


lemma idealsOverPrime_card_le {p : ℕ} (hp : p.Prime) :
    (idealsOverPrime K p).card ≤ Module.finrank ℤ (𝓞 K) := by
  exact (Multiset.toFinset_card_le _).trans
    (ideal_factor_count_le K hp (Ideal.absNorm_span_natCast p))


lemma decode_padMultiset {α : Type*} (s : Finset α) (r : ℕ) (m : Multiset α)
    (hm : ∀x ∈ m, x ∈ s) (hr : m.card ≤ r) :
    (padMultiset s r m hm hr).val.filterMap (Option.map Subtype.val) = m := by
  simp only [padMultiset, Multiset.filterMap_add, Multiset.filterMap_map]
  have hnone : ∀k, (Multiset.replicate k (none : Option s)).filterMap
      (Option.map Subtype.val) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Multiset.replicate_succ, Multiset.filterMap_cons_none _ _ rfl, ih]
  rw [hnone, add_zero]
  change m.attach.filterMap (some ∘ Subtype.val) = m
  rw [Multiset.filterMap_eq_map, Multiset.attach_map_val]

lemma card_le_of_multiset_encoding {α β : Type*} (s : Finset β) (r : ℕ)
    (f : α → Multiset β) (hf : Function.Injective f)
    (hs : ∀a x, x ∈ f a → x ∈ s) (hr : ∀a, (f a).card ≤ r) :
    Nat.card α ≤ (s.card + 1).multichoose r := by
  let g : α → Sym (Option s) r := fun a => padMultiset s r (f a) (hs a) (hr a)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    have H := congrArg (fun v : Sym (Option s) r =>
      v.val.filterMap (Option.map Subtype.val)) hab
    simpa only [g, decode_padMultiset] using H
  have H := Nat.card_le_card_of_injective g hg
  rw [Sym.natCard_sym_eq_multichoose] at H
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe] using H

 

lemma idealCoefficient_prime_pow_le {p : ℕ} (hp : p.Prime) (r : ℕ) :
    idealCoefficient K (p^r) ≤ (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
  rw [idealCoefficient_pos K _ (pow_ne_zero _ hp.ne_zero)]
  let f : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r} → Multiset (Ideal (𝓞 K)) :=
    fun I => normalizedFactors I.1
  have hzero : ∀I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r}, I.1 ≠ ⊥ := by
    intro I h
    have H : (0:ℕ) = p^r := by simpa [h] using I.2
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have hf : Function.Injective f := by
    intro I J h
    apply Subtype.ext
    have H := congrArg Multiset.prod h
    simpa only [f, Ideal.prod_normalizedFactors_eq_self (hzero I),
      Ideal.prod_normalizedFactors_eq_self (hzero J)] using H
  have H := card_le_of_multiset_encoding (idealsOverPrime K p) r f hf
    (fun I _ hP => ideal_factor_mem_over K hp I.2 hP)
    (fun I => ideal_factor_count_le K hp I.2)
  apply H.trans
  rw [Nat.multichoose_eq]
  calc
    _ ≤ (Module.finrank ℤ (𝓞 K) + r).choose r :=
      Nat.choose_le_choose r (by have := idealsOverPrime_card_le K hp; omega)
    _ = (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
      rw [Nat.add_comm (Module.finrank ℤ (𝓞 K)) r, Nat.choose_symm_add]


open Filter Topology Asymptotics

lemma idealCoefficientReal_nonneg (m : ℕ) : 0 ≤ idealCoefficientReal K m := Nat.cast_nonneg _


end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalMoments
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.HilbertRamification.Dedekind.basePrime_isPrime _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_finite_residue _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionFixedMaximalIdeal.instIsMaximal _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets

 
theorem haar_submodule_eq_inv_cardQuot {R A : Type*} [Ring R] [AddCommGroup A]
    [Module R A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule R A) [Finite (A ⧸ L)] (hL : MeasurableSet (L : Set A)) :
    μ (L : Set A) = (L.cardQuot : ℝ≥0∞)⁻¹ := by
  have : L.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (A ⧸ L)))
  have hc : (L.cardQuot : ℝ≥0∞) ≠ 0 := by
    rw [Submodule.cardQuot_apply]
    exact_mod_cast Nat.card_pos.ne'
  rw [← one_div (L.cardQuot : ℝ≥0∞)]
  apply (ENNReal.eq_div_iff hc (by simp)).mpr
  exact L.toAddSubgroup.index_mul_measure hL μ |>.trans (by simp)

end PrimeDegreePackets


open MeasureTheory Set IsDiscreteValuationRing
namespace PrimeDegreePackets

section DVR
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [MeasurableSpace R] [MeasurableAdd R]
    [Finite (IsLocalRing.ResidueField R)]
    (μ : Measure R) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

 
theorem haar_dvr_ideal_pow (k : ℕ)
    (hM : MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) =
      ((Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ^ k)⁻¹ := by
  have : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  rw [haar_submodule_eq_inv_cardQuot μ _ hM, cardQuot_pow_of_prime]
  · rw [Nat.cast_pow]
    rfl
  · exact fun h => IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

omit [MeasurableSpace R] [MeasurableAdd R] [Finite (IsLocalRing.ResidueField R)] in
 
lemma dvr_shell_eq_sdiff (k : ℕ) :
    {x : R | addVal R x = k} =
      ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) \
      ((IsLocalRing.maximalIdeal R ^ (k + 1) : Ideal R) : Set R) := by
  ext x
  simp only [Set.mem_sdiff, SetLike.mem_coe, mem_ofPred_eq, mem_maximalIdeal_pow_iff_addVal]
  induction addVal R x using ENat.recTopCoe with
  | top => simp
  | coe v => simp only [ENat.natCast_le_natCast, ENat.natCast_inj]; omega

 
theorem haar_dvr_shell (k : ℕ)
    (hM : ∀ k : ℕ, MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ {x : R | addVal R x = k} =
      (1 - (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞)⁻¹) /
      (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ^ k := by
  have hsub : ((IsLocalRing.maximalIdeal R ^ (k + 1) : Ideal R) : Set R) ⊆
      ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal R ^ (k + 1) at hx
    change x ∈ IsLocalRing.maximalIdeal R ^ k
    rw [mem_maximalIdeal_pow_iff_addVal] at hx ⊢
    exact (ENat.natCast_le_natCast.mpr (Nat.le_succ k)).trans hx
  have hq : (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [dvr_shell_eq_sdiff, measure_sdiff hsub (hM _).nullMeasurableSet (measure_ne_top μ _),
    haar_dvr_ideal_pow μ k (hM k), haar_dvr_ideal_pow μ (k + 1) (hM _),
    pow_succ, ENNReal.mul_inv (by simp) (by simp [hq]), div_eq_mul_inv, ENNReal.sub_mul (by simp [hq])]
  simp [mul_comm]

end DVR
end PrimeDegreePackets


namespace PrimeDegreePackets

section Algebra
variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]


lemma productDVRShell_eq_pi (k : ι → ℕ) :
    productDVRShell R k = Set.univ.pi (fun i => {x : R i | addVal (R i) x = k i}) := by
  ext x
  simp [productDVRShell]

lemma productDVRShell_smul_iff (k : ι → ℕ) (u : (∀ i, R i)ˣ) (x : ∀ i, R i) :
    u • x ∈ productDVRShell R k ↔ x ∈ productDVRShell R k := by
  have hu (i : ι) : addVal (R i) (u.val i) = 0 :=
    addVal_eq_zero_of_unit (MulEquiv.piUnits u i)
  change (∀ i, addVal (R i) (u.val i * x i) = k i) ↔ _
  simp only [addVal_mul, hu, zero_add]
  rfl

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

lemma productDVRShell_pairwiseDisjoint : Pairwise (fun k l => Disjoint (productDVRShell R k) (productDVRShell R l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hl
  apply hkl
  funext i
  exact ENat.natCast_inj.mp ((hx i).symm.trans (hl i))

lemma mem_iUnion_productDVRShell_iff (x : ∀ i, R i) :
    x ∈ ⋃ k : ι → ℕ, productDVRShell R k ↔ ∀ i, x i ≠ 0 := by
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    have := hk i
    rw [hi, addVal_zero] at this
    exact ENat.top_ne_natCast (k i) this
  · intro hx
    refine ⟨fun i => (addVal (R i) (x i)).toNat, ?_⟩
    intro i
    exact (ENat.natCast_toNat (fun h => hx i (addVal_eq_top_iff.mp h))).symm

end Algebra

section Measurability
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

omit [Fintype ι] in
lemma measurableSet_dvr_shell (i : ι) (k : ℕ) :
    MeasurableSet {x : R i | addVal (R i) x = k} := by
  have hset : {x : R i | addVal (R i) x = k} =
      ((IsLocalRing.maximalIdeal (R i) ^ k : Ideal (R i)) : Set (R i)) \
      ((IsLocalRing.maximalIdeal (R i) ^ (k + 1) : Ideal (R i)) : Set (R i)) := by
    ext x
    simp only [Set.mem_sdiff, SetLike.mem_coe, mem_ofPred_eq, mem_maximalIdeal_pow_iff_addVal]
    induction addVal (R i) x using ENat.recTopCoe with
    | top => simp
    | coe v => simp only [ENat.natCast_le_natCast, ENat.natCast_inj]; omega
  rw [hset]
  exact (IsLocalRing.isOpen_maximalIdeal_pow (R i) k).measurableSet.diff
    (IsLocalRing.isOpen_maximalIdeal_pow (R i) (k + 1)).measurableSet

lemma measurableSet_productDVRShell (k : ι → ℕ) : MeasurableSet (productDVRShell R k) := by
  rw [productDVRShell_eq_pi]
  exact MeasurableSet.univ_pi (fun i => measurableSet_dvr_shell R i (k i))

end Measurability
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

lemma product_shell_mass
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddLeftInvariant] (k : ι → ℕ) :
    Measure.pi μ (productDVRShell R k) = localZinv R / shellNorm R k := by
  rw [productDVRShell_eq_pi, Measure.pi_pi]
  have hM (i : ι) (j : ℕ) :
      MeasurableSet ((IsLocalRing.maximalIdeal (R i) ^ j : Ideal (R i)) : Set (R i)) :=
    (IsLocalRing.isOpen_maximalIdeal_pow (R i) j).measurableSet
  simp_rw [haar_dvr_shell _ _ (hM _)]
  exact ENNReal.prod_div_distrib_of_ne_top (by simp)

omit [∀ i, BorelSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma localZinv_ne_zero : localZinv R ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hq : (1 : ℝ≥0∞) < Nat.card (IsLocalRing.ResidueField (R i)) := by
    let := Fintype.ofFinite (IsLocalRing.ResidueField (R i))
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card (IsLocalRing.ResidueField (R i)))
  apply ne_of_gt
  exact tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr hq)

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma localZinv_ne_top : localZinv R ≠ ∞ := by
  apply ENNReal.prod_ne_top
  intro i _
  exact ne_of_lt ((tsub_le_self).trans_lt (by simp))

omit [∀ i, BorelSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_ne_zero (k : ι → ℕ) : shellNorm R k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply pow_ne_zero
  exact_mod_cast (Nat.card_pos : 0 < Nat.card (IsLocalRing.ResidueField (R i))).ne'

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_ne_top (k : ι → ℕ) : shellNorm R k ≠ ∞ := by
  apply ENNReal.prod_ne_top
  intro i _
  exact ENNReal.pow_ne_top (by simp)

end
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
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing Filter
open scoped ENNReal

 
theorem haar_dvr_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    [MeasurableSpace R] [MeasurableAdd R]
    (μ : Measure R) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (hM : ∀ k : ℕ, MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ {0} = 0 := by
  let := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have hq : (1 : ℝ≥0∞) < Nat.card (IsLocalRing.ResidueField R) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card (IsLocalRing.ResidueField R))
  have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr hq)
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' hlim
  intro k
  calc
    μ {0} ≤ μ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
      apply measure_mono
      intro x hx
      simp only [mem_singleton_iff] at hx
      simp [hx]
    _ = _ := by rw [haar_dvr_ideal_pow μ k (hM k), ENNReal.inv_pow]

end PrimeDegreePackets


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

 

theorem orbitContainmentProbability_mul_shell_measure
    (μ : Measure X) [IsFiniteMeasure μ] [SMulInvariantMeasure G X μ]
    (S L : Set X) (hS : MeasurableSet S) (hL : MeasurableSet L)
    (hinv : ∀ (g : G) (x : X), g • x ∈ S ↔ x ∈ S)
    (x₀ : X) (htrans : ∀ x ∈ S, ∃ g : G, g • x₀ = x) :
    orbitContainmentProbability ν L x₀ * μ S = μ (L ∩ S) := by
  have hconstant (x : X) (hx : x ∈ S) :
      orbitContainmentProbability ν L x = orbitContainmentProbability ν L x₀ := by
    obtain ⟨g, rfl⟩ := htrans x hx
    exact orbitContainmentProbability_smul ν L x₀ g
  have hfun : Measurable (fun (z : X × G) =>
      L.indicator (fun _ => (1 : ℝ≥0∞)) (z.2 • z.1)) :=
    (measurable_const.indicator hL).comp (measurable_snd.smul measurable_fst)
  calc
    orbitContainmentProbability ν L x₀ * μ S =
        ∫⁻ x in S, orbitContainmentProbability ν L x ∂μ := by
      rw [← setLIntegral_const]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with x hx
      exact (hconstant x hx).symm
    _ = ∫⁻ g, ∫⁻ x in S, L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) ∂μ ∂ν :=
      lintegral_lintegral_swap hfun.aemeasurable
    _ = ∫⁻ _g, μ (L ∩ S) ∂ν := by
      apply lintegral_congr
      intro g
      have heq : (fun x => L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) =
          ((g • ·) ⁻¹' L).indicator (fun _ => (1 : ℝ≥0∞)) := by
        ext x
        rfl
      rw [heq, show (fun _ : X => (1 : ℝ≥0∞)) = (1 : X → ℝ≥0∞) from rfl,
        lintegral_indicator_one (hL.preimage (measurable_const_smul g)),
        Measure.restrict_apply (hL.preimage (measurable_const_smul g))]
      have hset : (g • ·) ⁻¹' L ∩ S = (g • ·) ⁻¹' (L ∩ S) := by
        ext x
        simp only [mem_inter_iff, mem_preimage, hinv]
      rw [hset, measure_preimage_smul]
    _ = μ (L ∩ S) := by simp

end Action
end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem lintegral_eq_tsum_shells {X κ : Type*} [MeasurableSpace X] [Countable κ]
    (μ : Measure X) (S : κ → Set X) (hS : ∀ k, MeasurableSet (S k))
    (hdisj : Pairwise (fun k l => Disjoint (S k) (S l)))
    (hfull : μ (⋃ k, S k)ᶜ = 0)
    (F : X → ℝ≥0∞) (w : κ → ℝ≥0∞) (hF : ∀ k x, x ∈ S k → F x = w k) :
    ∫⁻ x, F x ∂μ = ∑' k, w k * μ (S k) := by
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ k, S k := by
    rw [ae_iff]
    exact hfull
  calc
    _ = ∫⁻ x in ⋃ k, S k, F x ∂μ := by
      rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∑' k, ∫⁻ x in S k, F x ∂μ := lintegral_iUnion hS hdisj F
    _ = _ := by
      apply tsum_congr
      intro k
      rw [← setLIntegral_const]
      apply setLIntegral_congr_fun (hS k)
      exact hF k

 
theorem restricted_lintegral_eq_tsum_shells {X κ : Type*}
    [MeasurableSpace X] [Countable κ]
    (μ : Measure X) (S : κ → Set X) (hS : ∀ k, MeasurableSet (S k))
    (hdisj : Pairwise (fun k l => Disjoint (S k) (S l)))
    (hfull : μ (⋃ k, S k)ᶜ = 0)
    (L : Set X) (F : X → ℝ≥0∞) (w : κ → ℝ≥0∞)
    (hF : ∀ k x, x ∈ S k → F x = w k) :
    ∫⁻ x in L, F x ∂μ = ∑' k, w k * μ (L ∩ S k) := by
  have hr : (μ.restrict L) (⋃ k, S k)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_le_self (μ := μ) (s := L) _).trans hfull.le) zero_le
  have he := lintegral_eq_tsum_shells (μ.restrict L) S hS hdisj hr F w hF
  simpa only [Measure.restrict_apply (hS _), inter_comm] using he

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma units_smulInvariant_addHaar {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
    [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] : SMulInvariantMeasure Rˣ R μ := by
  constructor
  intro u S hS
  let f : R ≃ₗ[R] R := LinearEquiv.smulOfUnit u
  have hf : MeasurePreserving f μ μ :=
    f.toAddMonoidHom.measurePreserving (by
      change Continuous (fun x : R => (u : R) * x)
      fun_prop) f.surjective rfl
  exact hf.measure_preimage hS.nullMeasurableSet

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

lemma productDVRShell_full_measure
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddLeftInvariant] :
    Measure.pi μ (⋃ k : ι → ℕ, productDVRShell R k)ᶜ = 0 := by
  have hzero (i : ι) : μ i {0} = 0 :=
    haar_dvr_zero (μ i) (fun k => (IsLocalRing.isOpen_maximalIdeal_pow (R i) k).measurableSet)
  have hnull (i : ι) : Measure.pi μ {x : ∀ i, R i | x i = 0} = 0 :=
    Measure.pi_eval_preimage_null μ (hzero i)
  have hset : (⋃ k : ι → ℕ, productDVRShell R k)ᶜ = ⋃ i, {x : ∀ i, R i | x i = 0} := by
    ext x
    rw [mem_compl_iff, mem_iUnion_productDVRShell_iff R x]
    simp
  rw [hset]
  exact measure_iUnion_null hnull



end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddHaarMeasure]
    (ν : Measure (∀ i, R i)ˣ) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

lemma localShellProbability_mul_mass (L : Set (∀ i, R i)) (hL : MeasurableSet L)
    (k : ι → ℕ) :
    localShellProbability R ν L k * (localZinv R / shellNorm R k) =
      Measure.pi μ (L ∩ productDVRShell R k) := by
  let : SMulInvariantMeasure (∀ i, R i)ˣ (∀ i, R i) (Measure.pi μ) :=
    units_smulInvariant_addHaar (Measure.pi μ)
  rw [← product_shell_mass R μ k]
  apply orbitContainmentProbability_mul_shell_measure ν (Measure.pi μ)
    (productDVRShell R k) L (measurableSet_productDVRShell R k) hL
    (productDVRShell_smul_iff R k)
  intro x hx
  exact productDVRShell_transitive R k (productDVRShell_nonempty R k).choose_spec hx

 
theorem local_weight_integral_identity (L : Set (∀ i, R i)) (hL : MeasurableSet L)
    (s : ℝ) :
    (∫⁻ x in L, shellNorm R (fun i => (addVal (R i) (x i)).toNat) ^ s ∂Measure.pi μ) =
      localZinv R * ∑' k : ι → ℕ,
        localShellProbability R ν L k * shellNorm R k ^ (s - 1) := by
  rw [restricted_lintegral_eq_tsum_shells (Measure.pi μ) (productDVRShell R)
    (measurableSet_productDVRShell R) (productDVRShell_pairwiseDisjoint R)
    (productDVRShell_full_measure R μ) L _ (fun k => shellNorm R k ^ s) (by
      intro k x hx
      congr 2
      funext i
      rw [hx i, ENat.toNat_natCast])]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [← localShellProbability_mul_mass R μ ν L hL k,
    ENNReal.rpow_sub s 1 (shellNorm_ne_zero R k) (shellNorm_ne_top R k),
    ENNReal.rpow_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddHaarMeasure]
    (ν : Measure (∀ i, R i)ˣ) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

include μ in
 
theorem local_weight_sum (p : ℕ) [Fact p.Prime] [∀ i, Algebra (PadicInt p) (R i)]
    (L : Submodule (PadicInt p) (∀ i, R i)) [Finite ((∀ i, R i) ⧸ L)]
    (hL : MeasurableSet (L : Set (∀ i, R i))) :
    (∑' k : ι → ℕ, localShellProbability R ν L k / shellNorm R k) =
      (L.cardQuot : ℝ≥0∞)⁻¹ / localZinv R := by
  apply (ENNReal.eq_div_iff (localZinv_ne_zero R) (localZinv_ne_top R)).mpr
  have hid := local_weight_integral_identity R μ ν L hL 0
  simpa only [ENNReal.rpow_zero, lintegral_one, Measure.restrict_apply_univ,
    haar_submodule_eq_inv_cardQuot (Measure.pi μ) L hL, zero_sub,
    ENNReal.rpow_neg_one, div_eq_mul_inv] using hid.symm

end
end PrimeDegreePackets

open Filter
open scoped BigOperators Topology
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeFactors
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.DiscreteNthRootsSubgroup.instTopologicalSpaceSubtypeUnitsMemSubgroup _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.boundedRealFields_finite _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.gLocallyCompact _root_.OAI.PrimeDegreePackets.gSecondCountable _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.model_units_measurableSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.OAI.PrimeDegreePackets.xLocallyCompact _root_.OAI.PrimeDegreePackets.xSecondCountable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteIdeleGroupIsTopologicalGroup _root_.finiteIdeleGroupLocallyCompactSpace _root_.finiteIdeleGroupT2Space _root_.finiteLocalUnitsOpen _root_.ideleGroupIsTopologicalGroup _root_.ideleGroupLocallyCompactSpace _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupLocallyCompactSpace _root_.infiniteIdeleGroupT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
universe v

lemma ennreal_tsum_fintype_prod {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℝ≥0∞),
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f
    simp
  · intro α _ ih κ f
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, ih]

 

lemma local_weight_product_factorization {ι : Type u} [Fintype ι]
    (κ : ι → Type v) (P d : ∀ i, κ i → ℝ≥0∞) (s : ℝ) :
    (∑' k : ∀ i, κ i, (∏ i, P i (k i)) * (∏ i, (d i (k i)) ^ s)) =
      ∏ i, ∑' k : κ i, P i k * d i k ^ s := by
  simp_rw [← Finset.prod_mul_distrib]
  exact ennreal_tsum_fintype_prod κ (fun i x => P i x * d i x ^ s)

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators


section
variable (n : ℕ) (S : Finset ℕ) [∀ p : S, Fact p.val.Prime]
    (ι : S → Type*) [∀ p, Fintype (ι p)]
    (R : ∀ p : S, ι p → Type*)
    [∀ p i, CommRing (R p i)] [∀ p i, IsDomain (R p i)]
    [∀ p i, IsDiscreteValuationRing (R p i)]
    [∀ p i, Algebra (PadicInt p.val) (R p i)]
    [∀ p i, TopologicalSpace (R p i)] [∀ p i, IsTopologicalRing (R p i)]
    [∀ p i, CompactSpace (R p i)] [∀ p i, T2Space (R p i)]
    [∀ p i, MeasurableSpace (R p i)] [∀ p i, BorelSpace (R p i)]
    [∀ p i, SecondCountableTopology (R p i)]
    [∀ p, MeasurableSpace (∀ i, R p i)ˣ] [∀ p, BorelSpace (∀ i, R p i)ˣ]
    (μ : ∀ p i, Measure (R p i)) [∀ p i, IsProbabilityMeasure (μ p i)]
    [∀ p i, (μ p i).IsAddHaarMeasure]
    (ν : ∀ p, Measure (∀ i, R p i)ˣ) [∀ p, IsProbabilityMeasure (ν p)]
    [∀ p, (ν p).IsMulRightInvariant]
    (L : ∀ p : S, Submodule (PadicInt p.val) (∀ i, R p i))
    [∀ p, Finite ((∀ i, R p i) ⧸ L p)]

include μ in
 
theorem global_local_weight_sum
    (hL : ∀ p, MeasurableSet (L p : Set (∀ i, R p i))) :
    (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k /
      packetLocalNorm S ι R k) =
      (localIndexProduct S ι R L : ℝ≥0∞)⁻¹ * ∏ p, (localZinv (R p))⁻¹ := by
  have hfactor := local_weight_product_factorization (fun p : S => ι p → ℕ)
    (fun p k => localShellProbability (R p) (ν p) (L p) k)
    (fun p k => shellNorm (R p) k) (-1)
  have hid : (∑' k : ∀ p, ι p → ℕ, packetLocalWeight S ι R ν L k /
      packetLocalNorm S ι R k) =
      ∏ p, ∑' k : ι p → ℕ, localShellProbability (R p) (ν p) (L p) k /
        shellNorm (R p) k := by
    unfold packetLocalWeight packetLocalNorm
    simp only [div_eq_mul_inv, ← ENNReal.rpow_neg_one]
    simpa only [ENNReal.prod_rpow_of_ne_top (fun p _ => shellNorm_ne_top (R p) _) (-1)] using hfactor
  rw [hid]
  simp_rw [local_weight_sum _ (μ _) (ν _) _ _ (hL _), div_eq_mul_inv]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [localIndexProduct, Nat.cast_prod]
  exact (ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by simp))).symm

end
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


theorem actual_tuple_weight_sum {n : ℕ} {K : Type u} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    (∑' k, actualTupleWeight M k / actualTupleNorm M k) =
      (saturationIndex M : ℝ≥0∞)⁻¹ * actualLocalZ M := by
  let T (p : labelPrimes M) := actualLocalModel p.val K
  let L (p : labelPrimes M) := modelLocalModule M p.val (T p).equiv
  let (p : labelPrimes M) : Finite ((∀ i, (T p).Ring i) ⧸ L p) :=
    modelLocalModule_finiteQuotient M hn p.val (T p).equiv
  have h := global_local_weight_sum (saturationIndex M).primeFactors
    (fun p => (T p).Index) (fun p => (T p).Ring)
    (fun p => modelAddHaarProbability (T p)) (fun p => modelUnitProbability p.val (T p).equiv)
    L (fun p => (modelLocalModule_open M hn p.val (T p).equiv (T p).continuous_symm).measurableSet)
  have hq : localIndexProduct (saturationIndex M).primeFactors (fun p => (T p).Index)
      (fun p => (T p).Ring) L = saturationIndex M := by
    unfold localIndexProduct
    dsimp only [L]
    simp_rw [modelLocalModule_cardQuot]
    exact (saturationIndex_eq_prod_integralNormalizedModule M hn).symm
  rw [hq] at h
  exact h

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

 

theorem primaryIdeal_reciprocal_sum_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) :
    (∑' J : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      globalIdealWeight M (nonzeroIntegralIdealUnit J.1) / (Ideal.absNorm J.1.1 : ℝ≥0∞)) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ * actualLocalZ M := by
  simp_rw [primaryIdeal_actual_weight M hn, primaryIdeal_actual_norm M]
  apply (ENNReal.tsum_comp_le_tsum_of_injective
    (primaryIdealValuations_injective (saturationIndex M).primeFactors
      (fun p => actualLocalModel p.val K))
    (fun k => actualTupleWeight M k / actualTupleNorm M k)).trans
  exact (actual_tuple_weight_sum M hn).le



end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IdealSupport
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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


namespace PrimeDegreePackets
open NumberField IsDiscreteValuationRing
open scoped BigOperators Pointwise NumberField nonZeroDivisors ENNReal


lemma integralIdeal_norm_eq_shell_product {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K)
    (J : primaryIntegralIdeals K S) :
    (Ideal.absNorm J.1.1 : ℝ≥0∞) =
      ∏ p : S, shellNorm (T p).Ring (primaryIdealValuations S T J p) := by
  rw [integralIdeal_norm_eq_valuation_product J.1 S J.2 T]
  simp only [Nat.cast_prod, Nat.cast_pow, shellNorm]
  apply Finset.prod_congr rfl
  intro p _
  apply Finset.prod_congr rfl
  intro i _
  rw [(T p).card_residue, Nat.cast_pow, pow_mul]
  rfl

lemma ennreal_inv_prod_finite {ι : Type*} (S : Finset ι) (f : ι → ℝ≥0∞)
    (hf : ∀ i ∈ S, f i ≠ ∞) : (∏ i ∈ S, f i)⁻¹ = ∏ i ∈ S, (f i)⁻¹ :=
  ENNReal.prod_inv_distrib (fun _ _ j hj _ => Or.inr (hf j hj))

lemma inverse_shellNorm_sum {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    (T : ActualLocalModel p K) :
    (∑' k : T.Index → ℕ, (shellNorm T.Ring k)⁻¹) = (localZinv T.Ring)⁻¹ := by
  classical
  simp only [shellNorm]
  have hprod (k : T.Index → ℕ) := ennreal_inv_prod_finite Finset.univ
    (fun i => (Nat.card (IsLocalRing.ResidueField (T.Ring i)) : ℝ≥0∞) ^ k i)
    (fun i _ => ENNReal.pow_ne_top (by simp))
  simp_rw [hprod, ENNReal.inv_pow]
  rw [ennreal_tsum_fintype_prod (fun _ : T.Index => ℕ)
    (fun i k => (Nat.card (IsLocalRing.ResidueField (T.Ring i)) : ℝ≥0∞)⁻¹ ^ k)]
  simp_rw [ENNReal.tsum_geometric]
  exact (ennreal_inv_prod_finite _ _ (fun i _ => ENNReal.sub_ne_top (by simp))).symm

 
theorem primaryIntegralIdeals_inverse_norm_series {K : Type*} [Field K] [NumberField K]
    (S : Finset ℕ) [∀ p : S, Fact p.val.Prime] (T : ∀ p : S, ActualLocalModel p.val K) :
    (∑' J : primaryIntegralIdeals K S, (Ideal.absNorm J.1.1 : ℝ≥0∞)⁻¹) =
      ∏ p : S, (localZinv (T p).Ring)⁻¹ := by
  classical
  simp_rw [integralIdeal_norm_eq_shell_product S T,
    ennreal_inv_prod_finite _ _ (fun p _ => shellNorm_ne_top (T p).Ring _)]
  calc
    _ = ∑' k : ∀ p : S, (T p).Index → ℕ, ∏ p : S, (shellNorm (T p).Ring (k p))⁻¹ :=
      (primaryIdealValuationEquiv S T).tsum_eq _
    _ = _ := by
      rw [ennreal_tsum_fintype_prod (fun p : S => (T p).Index → ℕ)
        (fun p k => (shellNorm (T p).Ring k)⁻¹)]
      simp_rw [inverse_shellNorm_sum]

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_MangoldtBounds
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.instTopologicalSpaceLocalAlgebra _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets


lemma multichoose_succ_eq (n k : ℕ) : (n+1).multichoose k = (k+n).choose n := by
  rw [Nat.multichoose_eq, show n+1+k-1 = k+n by omega]
  rw [← Nat.choose_symm (show k ≤ k+n by omega)]
  congr 1
  omega

lemma summable_multichoose_geometric (n : ℕ) :
    Summable (fun k : ℕ => ((n+1).multichoose k : ℝ) * (1/2:ℝ)^k) := by
  simp_rw [multichoose_succ_eq]
  exact summable_choose_mul_geometric_of_norm_lt_one n
    (by norm_num : ‖(1/2:ℝ)‖ < 1)

variable (K : Type*) [Field K] [NumberField K]



lemma idealPrimeEuler_summable {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => idealCoefficientReal K (p^k) / (p:ℝ)^k) := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply Summable.of_nonneg_of_le
    (fun _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
    (fun k => ?_) (summable_multichoose_geometric (Module.finrank ℤ (𝓞 K)))
  calc
    _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose k : ℕ) : ℝ) / (p:ℝ)^k := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      change (idealCoefficient K (p^k) : ℝ) ≤ _
      rw [multichoose_succ_eq]
      exact_mod_cast idealCoefficient_prime_pow_le K hp k
    _ ≤ (((Module.finrank ℤ (𝓞 K)+1).multichoose k : ℕ) : ℝ) / (2:ℝ)^k := by
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (pow_le_pow_left₀ (by norm_num) hp2 k)
    _ = _ := by simp [div_eq_mul_inv, ←inv_pow]

lemma idealPrimeEuler_one_le {p : ℕ} (hp : p.Prime) :
    1 ≤ idealPrimeEuler K p := by
  have H := (idealPrimeEuler_summable K hp).sum_le_tsum {0}
    (fun _ _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
  simpa [idealPrimeEuler,idealCoefficientReal,idealCoefficient_one] using H



lemma badPrimeEuler_pos (q : ℕ) : 0 < badPrimeEuler K q := by
  apply Finset.prod_pos
  intro p hp
  exact lt_of_lt_of_le zero_lt_one
    (idealPrimeEuler_one_le K (Nat.prime_of_mem_primeFactors hp))

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_PrimeSums
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid


namespace PrimeDegreePackets
open scoped ENNReal


variable (K : Type*) [Field K] [NumberField K]

lemma primary_ideal_inverse_norm_series {p : ℕ} (hp : p.Prime) :
    (∑' I : PrimaryIdeal K p, ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ)⁻¹)) =
      ENNReal.ofReal (idealPrimeEuler K p) := by
  classical
  rw [←(primaryIdealNormEquiv K p hp).tsum_eq]
  simp only [primaryIdealNormEquiv_val]
  rw [ENNReal.tsum_sigma (fun e (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e}) =>
    ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ)⁻¹))]
  rw [idealPrimeEuler,ENNReal.ofReal_tsum_of_nonneg
    (fun _ => div_nonneg (idealCoefficientReal_nonneg K _) (by positivity))
      (idealPrimeEuler_summable K hp)]
  apply tsum_congr
  intro e
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} :=
    (Ideal.finite_setOfPred_absNorm_eq _).to_subtype
  let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} := Fintype.ofFinite _
  have HE : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} =>
    ENNReal.ofReal ((Ideal.absNorm I.1 : ℝ)⁻¹)) =
      fun _ => ENNReal.ofReal (((p:ℝ)^e)⁻¹) := by
    funext I
    rw [I.2,Nat.cast_pow]
  rw [HE,tsum_fintype,sum_const]
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk,
    idealCoefficient_pos K _ (pow_ne_zero _ hp.ne_zero),Nat.card_eq_fintype_card]
  have hpR : (0:ℝ) < p := Nat.cast_pos.mpr hp.pos
  rw [ENNReal.ofReal_div_of_pos (pow_pos hpR e),
    ENNReal.ofReal_inv_of_pos (pow_pos hpR e)]
  simp only [nsmul_eq_mul,div_eq_mul_inv]
  simp

end PrimeDegreePackets
end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_LocalEuler
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets
open NumberField
open scoped BigOperators ENNReal nonZeroDivisors



theorem actual_localZ_eq_idealPrimeEuler (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    (localZinv (actualLocalModel p K).Ring)⁻¹ = ENNReal.ofReal (idealPrimeEuler K p) := by
  classical
  let S : Finset ℕ := {p}
  let : ∀ r : S, Fact r.val.Prime := fun r => ⟨by
    have hr : r.val = p := Finset.mem_singleton.mp r.2
    simpa [hr] using (Fact.out : p.Prime)⟩
  let : Unique S := ⟨⟨⟨p,by simp [S]⟩⟩,fun r => Subtype.ext (Finset.mem_singleton.mp r.2)⟩
  have h := primaryIntegralIdeals_inverse_norm_series S (fun r => actualLocalModel r.val K)
  rw [Fintype.prod_unique] at h
  change (∑' J : primaryIntegralIdeals K {p}, (Ideal.absNorm J.1.1 : ℝ≥0∞)⁻¹) =
    (localZinv (actualLocalModel p K).Ring)⁻¹ at h
  rw [← h]
  have he : (∑' J : primaryIntegralIdeals K {p}, (Ideal.absNorm J.1.1 : ℝ≥0∞)⁻¹) =
      ∑' I : PrimaryIdeal K p, (Ideal.absNorm I.1 : ℝ≥0∞)⁻¹ :=
    (primaryIdealSingletonEquiv K p Fact.out).tsum_eq
      (fun I : PrimaryIdeal K p => (Ideal.absNorm I.1 : ℝ≥0∞)⁻¹)
  rw [he]
  convert primary_ideal_inverse_norm_series K (Fact.out : p.Prime) using 1
  all_goals try with_reducible_and_instances rfl
  apply tsum_congr
  intro I
  rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.2.1)))]
  simp

theorem actualLocalZ_eq_badPrimeEuler {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) : actualLocalZ M = ENNReal.ofReal (badPrimeEuler K (saturationIndex M)) := by
  classical
  unfold actualLocalZ badPrimeEuler
  simp_rw [actual_localZ_eq_idealPrimeEuler]
  rw [ENNReal.ofReal_prod_of_nonneg (fun p hp =>
    (idealPrimeEuler_one_le K (Nat.prime_of_mem_primeFactors hp)).trans' zero_le_one)]
  exact Finset.prod_coe_sort (saturationIndex M).primeFactors
    (fun p : ℕ => ENNReal.ofReal (idealPrimeEuler K p))

end PrimeDegreePackets


end
end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.PrimePackets_IntervalGeometry
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

lemma cast_div_gt_sub_one (m d : ℕ) (hd : 0 < d) :
    (m:ℝ)/d - 1 < (m/d : ℕ) := by
  have hmod : ((m%d : ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt m hd
  have heq : (d:ℝ)*(m/d : ℕ) + (m%d : ℕ) = m := by exact_mod_cast Nat.div_add_mod m d
  have H : (m:ℝ)/d < (m/d : ℕ)+1 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hd)).mpr
    nlinarith
  linarith

lemma cast_div_interval_bounds (a b d : ℕ) (hd : 0 < d) :
    ((b:ℝ)-a)/d - 1 ≤ ((b/d : ℕ):ℝ)-(a/d : ℕ) ∧
      ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ ((b:ℝ)-a)/d + 1 := by
  have ha := cast_div_gt_sub_one a d hd
  have hb := cast_div_gt_sub_one b d hd
  have ha' : ((a/d : ℕ):ℝ) ≤ (a:ℝ)/d := Nat.cast_div_le
  have hb' : ((b/d : ℕ):ℝ) ≤ (b:ℝ)/d := Nat.cast_div_le
  rw [sub_div]
  constructor <;> linarith

lemma cast_div_interval_relative (a b d : ℕ) (hd : 0 < d)
    (η : ℝ) (hη : 0 < η) (hrel : η*b ≤ (b:ℝ)-a)
    (hlong : 2 ≤ η*(b/d : ℕ)) :
    (η/2)*(b/d : ℕ) ≤ ((b/d : ℕ):ℝ)-(a/d : ℕ) := by
  have H := (cast_div_interval_bounds a b d hd).1
  have hdR : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hob : η*(b/d : ℕ) ≤ ((b:ℝ)-a)/d := by
    calc
      _ ≤ η*((b:ℝ)/d) := mul_le_mul_of_nonneg_left Nat.cast_div_le hη.le
      _ = (η*b)/d := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hrel hdR.le
  nlinarith

lemma cast_div_interval_width (a b d : ℕ) (hd : 0 < d)
    (hwidth : (d:ℝ) ≤ (b:ℝ)-a) :
    ((b/d : ℕ):ℝ)-(a/d : ℕ) ≤ 2*((b:ℝ)-a)/d := by
  have H := (cast_div_interval_bounds a b d hd).2
  have H' : (1:ℝ) ≤ ((b:ℝ)-a)/d := (le_div_iff₀ (Nat.cast_pos.mpr hd)).mpr (by simpa using hwidth)
  calc
    _ ≤ ((b:ℝ)-a)/d+1 := H
    _ ≤ 2*(((b:ℝ)-a)/d) := by linarith
    _ = _ := by ring

lemma div_square_lower {b d : ℕ} (hd : 0 < d) (hbd : 4*d^2 ≤ b) :
    2 ≤ b/d ∧ b ≤ (b/d)^2 := by
  have hu4 : 4*d ≤ b/d := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
  have hu : 0 < b/d := by omega
  have hmod : b%d ≤ d := (Nat.mod_lt b hd).le
  have heq := Nat.div_add_mod b d
  refine ⟨by omega,?_⟩
  calc
    b = (b/d)*d+b%d := by nlinarith [heq]
    _ ≤ (b/d)*d+d := Nat.add_le_add_left hmod _
    _ ≤ (b/d)*d+(b/d)*d := Nat.add_le_add_left (Nat.le_mul_of_pos_left d hu) _
    _ = (b/d)*(2*d) := by ring
    _ ≤ (b/d)*(b/d) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end PrimeDegreePackets


namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors



theorem weightedIdeal_small_norm_bound_oai (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K]
        (M : FullLattice n K), Module.finrank ℚ K = n →
        ∀ a b T : ℕ, 0 < T → R ≤ b/T →
          Real.log (saturationIndex M) ≤ (b/T : ℕ) →
          4*T^2 ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
          2 ≤ η*(b/T : ℕ) →
          (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
            if Ideal.absNorm I.1.1 ≤ T then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) *
              ENNReal.ofReal (∑ m ∈ Ioc (a / Ideal.absNorm I.1.1) (b / Ideal.absNorm I.1.1),
                coprimeIdealCoefficient K (saturationIndex M) m) else 0) ≤
          (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C * ((b:ℝ)-a) *
              ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b)) := by
  classical
  obtain ⟨C,hC,hInt⟩ := coprime_ideal_scaled_interval n
  refine ⟨C,hC,?_⟩
  intro η hη
  obtain ⟨R,hR⟩ := hInt (η/2) (by positivity)
  refine ⟨R,?_⟩
  intro K _ _ M hn a b T hT hRT hqT hsq hab hrel hlong
  have hnZ : Module.finrank ℤ (𝓞 K) = n := by rw [NumberField.RingOfIntegers.rank]; exact hn
  have hq : 0 < saturationIndex M := Nat.pos_of_ne_zero (saturationIndex_ne_zero M)
  have hwide : (T:ℝ) ≤ (b:ℝ)-a := by
    have H : 2 ≤ ((b:ℝ)-a)/T := by
      calc
        _ ≤ η*(b/T : ℕ) := hlong
        _ ≤ η*((b:ℝ)/T) := mul_le_mul_of_nonneg_left Nat.cast_div_le hη.le
        _ = (η*b)/T := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hrel (Nat.cast_nonneg _)
    have H' := (le_div_iff₀ (Nat.cast_pos.mpr hT)).mp H
    linarith [show (0:ℝ) ≤ T by positivity]
  let B : ℝ := C * ((b:ℝ)-a) *
    ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b)
  let E : ℝ := badPrimeEuler K (saturationIndex M)
  have hE : 0 < E := badPrimeEuler_pos K _
  have hZ : actualLocalZ M = ENNReal.ofReal E := actualLocalZ_eq_badPrimeEuler M
  calc
    _ ≤ ENNReal.ofReal (B/E) *
        ∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
          globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞) := by
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro I
      split_ifs with hIT
      · have hd : 0 < Ideal.absNorm I.1.1 :=
          Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.1.2)
        have huT : b/T ≤ b/Ideal.absNorm I.1.1 := Nat.div_le_div_left hIT hd
        have huR : ((b/T : ℕ):ℝ) ≤ (b/Ideal.absNorm I.1.1 : ℕ) := by exact_mod_cast huT
        have hlongI : 2 ≤ η*(b/Ideal.absNorm I.1.1 : ℕ) :=
          hlong.trans (mul_le_mul_of_nonneg_left huR hη.le)
        have hsqI : 4*(Ideal.absNorm I.1.1)^2 ≤ b := by
          exact (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hIT 2)).trans hsq
        have H := hR K hnZ (saturationIndex M) a b (Ideal.absNorm I.1.1) hq hd
          (hqT.trans huR) (hRT.trans huT) hab
          (cast_div_interval_relative a b _ hd η hη hrel hlongI)
          (div_square_lower hd hsqI).2
          (cast_div_interval_width a b _ hd
            ((show (Ideal.absNorm I.1.1 : ℝ) ≤ T by exact_mod_cast hIT).trans hwide))
        have H' := ENNReal.ofReal_le_ofReal H
        refine (mul_le_mul_right H' _).trans_eq ?_
        have heq : C * (((b:ℝ)-a)/Ideal.absNorm I.1.1) *
            ((NumberField.dedekindZeta K (1+1/Real.log b)).re / Real.log b) /
              badPrimeEuler K (saturationIndex M) = (B/E)/Ideal.absNorm I.1.1 := by
          dsimp only [B,E]
          ring
        rw [heq, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hd), ENNReal.ofReal_natCast]
        simp only [div_eq_mul_inv]
        ac_rfl
      · exact bot_le
    _ ≤ ENNReal.ofReal (B/E) * ((saturationIndex M : ℝ≥0∞)⁻¹ * actualLocalZ M) :=
      mul_le_mul_right (primaryIdeal_reciprocal_sum_le M hn) _
    _ = _ := by
      rw [hZ, ENNReal.ofReal_div_of_pos hE]
      have hE0 : ENNReal.ofReal E ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hE)
      have hEt : ENNReal.ofReal E ≠ ∞ := ENNReal.ofReal_ne_top
      calc
        ENNReal.ofReal B / ENNReal.ofReal E *
            ((saturationIndex M : ℝ≥0∞)⁻¹ * ENNReal.ofReal E) =
          (saturationIndex M : ℝ≥0∞)⁻¹ *
            ((ENNReal.ofReal B / ENNReal.ofReal E) * ENNReal.ofReal E) := by ac_rfl
        _ = _ := by rw [ENNReal.div_mul_cancel hE0 hEt]

end PrimeDegreePackets


end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PrimeDegreePackets.weightedIdeal_small_norm_bound_oai.{u_1} := @OAI.PrimeDegreePackets.weightedIdeal_small_norm_bound_oai.{u_1}
