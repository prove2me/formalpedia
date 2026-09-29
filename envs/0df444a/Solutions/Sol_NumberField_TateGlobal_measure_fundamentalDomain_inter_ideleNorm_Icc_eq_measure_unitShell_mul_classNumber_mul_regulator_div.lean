-- Prove2me | solution 1 for NumberField.TateGlobal.measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/528dc209-629a-546b-94f1-28b548f0ce24

import Theorems.Thm_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField IsDedekindDomain"
open scoped Pointwise ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "classNumber_pos mk place Units.torsionOrder InfinitePlace.nrComplexPlaces InfinitePlace AdeleRing Units.regulator classNumber TateGlobal.measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div TateGlobal.ideleNorm TateGlobal.ideleNorm_pos TateGlobal.ideleNorm_mul AdeleRing.unitIdelesOutside TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber TateGlobal.continuous_ideleNorm AdeleRing.distribHaarChar_algebraMap Idele.isOpen_unitIdelesOutside"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div ideleNorm ideleNorm_pos ideleNorm_mul index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber continuous_ideleNorm"
namespace ClassNumberVolumeReduce
p2m_open "NumberField.TateGlobal NumberField"

variable (K : Type) [Field K] [NumberField K]

abbrev Kx : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range

abbrev U : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K)))

abbrev E : Subgroup (AdeleRing (𝓞 K) K)ˣ := Kx K ⊓ U K

abbrev H : Subgroup (AdeleRing (𝓞 K) K)ˣ := U K ⊔ Kx K

def band (a b : ℝ) : Set (AdeleRing (𝓞 K) K)ˣ := {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}

def shell : Set (AdeleRing (𝓞 K) K)ˣ :=
  {u | (∀ v : HeightOneSpectrum (𝓞 K),
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
      (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K) ∧
    ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}

def cst : ℝ :=
  NumberField.Units.regulator K /
    (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))

theorem countable_field : Countable K := by
  let b := Module.finBasis ℚ K
  exact Function.Injective.countable b.equivFun.injective

scoped instance countable_Kx : Countable (Kx K) := by
  haveI := countable_field K
  haveI : Countable Kˣ := Function.Injective.countable (Units.val_injective (α := K))
  have h : ((Kx K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem ideleNorm_Kx (k : Kx K) : NumberField.TateGlobal.ideleNorm K (k : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  obtain ⟨_, a, rfl⟩ := k
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have h : distribHaarChar (AdeleRing (𝓞 K) K)
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap K a
  simp only [NumberField.TateGlobal.ideleNorm, h, NNReal.coe_one]

theorem mem_band {a b : ℝ} {x : (AdeleRing (𝓞 K) K)ˣ} :
    x ∈ band K a b ↔ NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b := Iff.rfl

theorem smul_band (x : (AdeleRing (𝓞 K) K)ˣ) {a b : ℝ} :
    x • band K (a / NumberField.TateGlobal.ideleNorm K x) (b / NumberField.TateGlobal.ideleNorm K x) =
      band K a b := by
  have hx : 0 < NumberField.TateGlobal.ideleNorm K x := NumberField.TateGlobal.ideleNorm_pos x
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_band, mem_band, smul_eq_mul,
    NumberField.TateGlobal.ideleNorm_mul, Set.mem_Icc, Set.mem_Icc]
  have hinv : NumberField.TateGlobal.ideleNorm K x⁻¹ = (NumberField.TateGlobal.ideleNorm K x)⁻¹ := by
    have h1 : NumberField.TateGlobal.ideleNorm K x⁻¹ * NumberField.TateGlobal.ideleNorm K x = 1 := by
      rw [← NumberField.TateGlobal.ideleNorm_mul, inv_mul_cancel]
      simp [NumberField.TateGlobal.ideleNorm]
    exact eq_inv_of_mul_eq_one_left h1
  rw [hinv, div_le_iff₀ hx, le_div_iff₀ hx]
  have hc : (NumberField.TateGlobal.ideleNorm K x)⁻¹ * NumberField.TateGlobal.ideleNorm K y *
      NumberField.TateGlobal.ideleNorm K x = NumberField.TateGlobal.ideleNorm K y := by
    field_simp
  rw [hc]

theorem Kx_smul_band (k : Kx K) (a b : ℝ) : k • band K a b = band K a b := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_band, mem_band, Subgroup.smul_def, smul_eq_mul,
    NumberField.TateGlobal.ideleNorm_mul]
  have : NumberField.TateGlobal.ideleNorm K ((k⁻¹ : Kx K) : (AdeleRing (𝓞 K) K)ˣ) = 1 := ideleNorm_Kx K k⁻¹
  rw [this, one_mul]

section Meas

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

theorem measurableSet_band (a b : ℝ) : MeasurableSet (band K a b) :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable measurableSet_Icc

theorem isOpen_U : IsOpen ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
  NumberField.Idele.isOpen_unitIdelesOutside K _

theorem measurableSet_U : MeasurableSet ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
  (isOpen_U K).measurableSet

theorem isOpen_H : IsOpen ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
  Subgroup.isOpen_mono (le_sup_left : U K ≤ H K) (isOpen_U K)

theorem measurableSet_H : MeasurableSet ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
  (isOpen_H K).measurableSet

scoped instance measurableConstSMul_Kx : MeasurableConstSMul (Kx K) (AdeleRing (𝓞 K) K)ˣ :=
  ⟨fun c => by
    show Measurable fun x : (AdeleRing (𝓞 K) K)ˣ => (c : (AdeleRing (𝓞 K) K)ˣ) * x
    exact measurable_const_mul _⟩

scoped instance measurableConstSMul_E : MeasurableConstSMul (E K) (AdeleRing (𝓞 K) K)ˣ :=
  ⟨fun c => by
    show Measurable fun x : (AdeleRing (𝓞 K) K)ˣ => (c : (AdeleRing (𝓞 K) K)ˣ) * x
    exact measurable_const_mul _⟩

scoped instance smulInvariant_Kx (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsMulLeftInvariant] :
    SMulInvariantMeasure (Kx K) (AdeleRing (𝓞 K) K)ˣ ν :=
  ⟨fun c s hs => by
    show ν ((fun x => (c : (AdeleRing (𝓞 K) K)ˣ) * x) ⁻¹' s) = ν s
    exact measure_preimage_mul ν _ s⟩

scoped instance smulInvariant_E (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsMulLeftInvariant] :
    SMulInvariantMeasure (E K) (AdeleRing (𝓞 K) K)ˣ ν :=
  ⟨fun c s hs => by
    show ν ((fun x => (c : (AdeleRing (𝓞 K) K)ˣ) * x) ⁻¹' s) = ν s
    exact measure_preimage_mul ν _ s⟩

scoped instance smulCommClass_Kx : SMulCommClass (AdeleRing (𝓞 K) K)ˣ (Kx K) (AdeleRing (𝓞 K) K)ˣ :=
  ⟨fun a k x => by
    show a * ((k : (AdeleRing (𝓞 K) K)ˣ) * x) = (k : (AdeleRing (𝓞 K) K)ˣ) * (a * x)
    rw [mul_left_comm]⟩

end Meas

section FD

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

def unitFD (Ω : Set (AdeleRing (𝓞 K) K)ˣ) (T : Set (Kx K)) : Set (AdeleRing (𝓞 K) K)ˣ :=
  ⋃ t : T, ((t : Kx K)⁻¹) • Ω

variable {K}

theorem eq_one_of_mul_eq {T : Set (Kx K)}
    (hT : Subgroup.IsComplement T ((E K).subgroupOf (Kx K) : Set (Kx K)))
    {t t' : T} {e : (E K).subgroupOf (Kx K)} (h : (t : Kx K) * (e : Kx K) = (t' : Kx K)) :
    e = 1 ∧ t = t' := by
  have h1 : ((t' : Kx K)) * ((1 : (E K).subgroupOf (Kx K)) : Kx K) = (t' : Kx K) := by
    rw [OneMemClass.coe_one, mul_one]
  obtain ⟨p, -, hp⟩ := hT.existsUnique (t' : Kx K)
  have e1 : (⟨t, e⟩ : T × ((E K).subgroupOf (Kx K))) = p := hp ⟨t, e⟩ h
  have e2 : (⟨t', 1⟩ : T × ((E K).subgroupOf (Kx K))) = p := hp ⟨t', 1⟩ h1
  have e3 := e1.trans e2.symm
  simp only [Prod.mk.injEq] at e3
  exact ⟨e3.2, e3.1⟩

theorem isFundamentalDomain_unitFD (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsMulLeftInvariant]
    {Ω : Set (AdeleRing (𝓞 K) K)ˣ} (hΩ : IsFundamentalDomain (Kx K) Ω ν) {T : Set (Kx K)}
    (hT : Subgroup.IsComplement T ((E K).subgroupOf (Kx K) : Set (Kx K))) :
    IsFundamentalDomain (E K) (unitFD K Ω T) ν := by
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact NullMeasurableSet.iUnion fun t => hΩ.nullMeasurableSet_smul _
  · filter_upwards [hΩ.ae_covers] with x hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨⟨t, e⟩, hte, -⟩ := hT.existsUnique k
    refine ⟨⟨((e : Kx K) : (AdeleRing (𝓞 K) K)ˣ), (Subgroup.mem_subgroupOf).1 e.2⟩, ?_⟩
    refine Set.mem_iUnion.2 ⟨t, ?_⟩
    have hek : (e : Kx K) = (t : Kx K)⁻¹ * k := by
      rw [← hte]; group
    have : (⟨((e : Kx K) : (AdeleRing (𝓞 K) K)ˣ), (Subgroup.mem_subgroupOf).1 e.2⟩ : E K) • x =
        (t : Kx K)⁻¹ • (k • x) := by
      rw [smul_smul, ← hek]; rfl
    rw [this]
    exact Set.smul_mem_smul_set hk
  · intro g hg

    set g' : Kx K := ⟨(g : (AdeleRing (𝓞 K) K)ˣ), g.2.1⟩ with hg'
    have hgE : g' ∈ (E K).subgroupOf (Kx K) := (Subgroup.mem_subgroupOf).2 g.2
    have hg'1 : g' ≠ 1 := by
      intro h
      apply hg
      ext
      have := congrArg (fun z : Kx K => (z : (AdeleRing (𝓞 K) K)ˣ)) h
      simpa [hg'] using this
    have hsmul : g • unitFD K Ω T = ⋃ t : T, (g' * (t : Kx K)⁻¹) • Ω := by
      have h1 : g • unitFD K Ω T = g' • unitFD K Ω T := rfl
      rw [h1, unitFD, Set.smul_set_iUnion]
      simp_rw [smul_smul]
    rw [hsmul, unitFD]
    refine (AEDisjoint.iUnion_left_iff).2 fun t => (AEDisjoint.iUnion_right_iff).2 fun t' => ?_
    refine hΩ.aedisjoint ?_
    intro heq

    have h2 : (t' : Kx K) * g' = (t : Kx K) := by
      have := congrArg (fun z => (t' : Kx K) * z * (t : Kx K)) heq
      simpa [mul_assoc] using this
    have := (eq_one_of_mul_eq hT (t := t') (t' := t) (e := ⟨g', hgE⟩) h2).1
    exact hg'1 (by simpa using congrArg (fun z : (E K).subgroupOf (Kx K) => (z : Kx K)) this)
  · intro g
    have : (fun x : (AdeleRing (𝓞 K) K)ˣ => g • x) = fun x => (g : (AdeleRing (𝓞 K) K)ˣ) * x := rfl
    rw [this]
    exact (measurePreserving_mul_left ν _).quasiMeasurePreserving

theorem disjoint_smul_U {T : Set (Kx K)}
    (hT : Subgroup.IsComplement T ((E K).subgroupOf (Kx K) : Set (Kx K))) {t t' : T} (h : t ≠ t') :
    Disjoint ((t : Kx K) • ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ))
      ((t' : Kx K) • ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨u', hu', hx⟩
  apply h

  set a : (AdeleRing (𝓞 K) K)ˣ := ((t : Kx K) : (AdeleRing (𝓞 K) K)ˣ) with ha
  set a' : (AdeleRing (𝓞 K) K)ˣ := ((t' : Kx K) : (AdeleRing (𝓞 K) K)ˣ) with ha'
  have hx' : a' * u' = a * u := hx
  have hmem : (((t' : Kx K)⁻¹ * (t : Kx K) : Kx K) : (AdeleRing (𝓞 K) K)ˣ) ∈ U K := by
    have : (((t' : Kx K)⁻¹ * (t : Kx K) : Kx K) : (AdeleRing (𝓞 K) K)ˣ) = u' * u⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← ha, ← ha']
      calc a'⁻¹ * a = a'⁻¹ * (a * u) * u⁻¹ := by group
        _ = a'⁻¹ * (a' * u') * u⁻¹ := by rw [hx']
        _ = u' * u⁻¹ := by group
    rw [this]
    exact mul_mem hu' (inv_mem hu)
  have hE : (t' : Kx K)⁻¹ * (t : Kx K) ∈ (E K).subgroupOf (Kx K) :=
    (Subgroup.mem_subgroupOf).2 ⟨((t' : Kx K)⁻¹ * (t : Kx K)).2, hmem⟩
  have h2 : (t' : Kx K) * (((⟨_, hE⟩ : (E K).subgroupOf (Kx K)) : Kx K)) = (t : Kx K) := by
    show (t' : Kx K) * ((t' : Kx K)⁻¹ * (t : Kx K)) = (t : Kx K)
    group
  exact ((eq_one_of_mul_eq hT h2).2).symm

theorem iUnion_smul_U {T : Set (Kx K)}
    (hT : Subgroup.IsComplement T ((E K).subgroupOf (Kx K) : Set (Kx K))) :
    (⋃ t : T, (t : Kx K) • ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) =
      ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := by
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · rintro ⟨t, u, hu, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right (t : Kx K).2) (Subgroup.mem_sup_left hu)
  · intro hx
    obtain ⟨u, hu, k, hk, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨⟨t, e⟩, hte, -⟩ := hT.existsUnique ⟨k, hk⟩
    refine ⟨t, u * ((e : Kx K) : (AdeleRing (𝓞 K) K)ˣ), mul_mem hu ((Subgroup.mem_subgroupOf).1 e.2).2, ?_⟩
    have hk' : k = ((t : Kx K) : (AdeleRing (𝓞 K) K)ˣ) * ((e : Kx K) : (AdeleRing (𝓞 K) K)ˣ) := by
      have := congrArg (fun z : Kx K => (z : (AdeleRing (𝓞 K) K)ˣ)) hte
      simpa using this.symm
    show ((t : Kx K) : (AdeleRing (𝓞 K) K)ˣ) * (u * _) = u * k
    rw [hk']
    simp only [mul_left_comm]

theorem measure_U_inter_unitFD (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsMulLeftInvariant]
    {Ω : Set (AdeleRing (𝓞 K) K)ˣ} (hΩ : IsFundamentalDomain (Kx K) Ω ν) {T : Set (Kx K)}
    (hT : Subgroup.IsComplement T ((E K).subgroupOf (Kx K) : Set (Kx K))) (a b : ℝ) :
    ν (((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ unitFD K Ω T ∩ band K a b) =
      ν (Ω ∩ band K a b ∩ ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) := by
  set Us : Set (AdeleRing (𝓞 K) K)ˣ := ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)

  have hset : Us ∩ unitFD K Ω T ∩ band K a b = ⋃ t : T, (Us ∩ ((t : Kx K)⁻¹ • Ω) ∩ band K a b) := by
    simp only [unitFD, Set.inter_iUnion, Set.iUnion_inter]
  rw [hset, measure_iUnion₀]
  rotate_left
  · intro t t' htt'
    have hne : (t : Kx K)⁻¹ ≠ (t' : Kx K)⁻¹ := fun h => htt' (Subtype.ext (inv_injective h))
    exact (hΩ.aedisjoint hne).mono (fun x hx => hx.1.2) (fun x hx => hx.1.2)
  · intro t
    exact ((measurableSet_U K).nullMeasurableSet.inter (hΩ.nullMeasurableSet_smul _)).inter
      (measurableSet_band K a b).nullMeasurableSet

  have hpiece : ∀ t : T, ν (Us ∩ ((t : Kx K)⁻¹ • Ω) ∩ band K a b) =
      ν (((t : Kx K) • Us) ∩ Ω ∩ band K a b) := by
    intro t
    rw [← measure_smul ν (t : Kx K) (Us ∩ ((t : Kx K)⁻¹ • Ω) ∩ band K a b), Set.smul_set_inter,
      Set.smul_set_inter, smul_inv_smul, Kx_smul_band]
  simp_rw [hpiece]
  rw [← measure_iUnion₀]
  · rw [← Set.iUnion_inter, ← Set.iUnion_inter, iUnion_smul_U hT, Set.inter_comm _ Ω, Set.inter_right_comm]
  · intro t t' htt'
    exact Disjoint.aedisjoint (((disjoint_smul_U hT htt').mono (fun x hx => hx.1.1) fun x hx => hx.1.1))
  · intro t
    exact (((measurableSet_U K).const_smul (t : Kx K)).nullMeasurableSet.inter hΩ.nullMeasurableSet).inter
      (measurableSet_band K a b).nullMeasurableSet

end FD

section Main

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

theorem exists_transversal :
    ∃ T : Set (Kx K), Subgroup.IsComplement T ((E K).subgroupOf (Kx K) : Set (Kx K)) := by
  obtain ⟨T, hT, -⟩ := Subgroup.exists_isComplement_left ((E K).subgroupOf (Kx K)) 1
  exact ⟨T, hT⟩

variable {K}

theorem measure_inter_band_inter_H (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [hν : ν.IsHaarMeasure]
    (hreg : ∀ F : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain (E K) F (ν.restrict ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν (((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩ band K a b) =
          ν (shell K) * ENNReal.ofReal (cst K) * ENNReal.ofReal (Real.log (b / a)))
    {Ω : Set (AdeleRing (𝓞 K) K)ˣ} (hΩ : IsFundamentalDomain (Kx K) Ω ν) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ν (Ω ∩ band K a b ∩ ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) =
      ν (shell K) * ENNReal.ofReal (cst K) * ENNReal.ofReal (Real.log (b / a)) := by
  obtain ⟨T, hT⟩ := exists_transversal K
  rw [← measure_U_inter_unitFD ν hΩ hT a b]
  refine hreg _ ?_ a b ha hab
  exact (isFundamentalDomain_unitFD ν hΩ hT).mono
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem measure_inter_band_inter_smul_H (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [hν : ν.IsHaarMeasure]
    (hreg : ∀ F : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain (E K) F (ν.restrict ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν (((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩ band K a b) =
          ν (shell K) * ENNReal.ofReal (cst K) * ENNReal.ofReal (Real.log (b / a)))
    {Ω : Set (AdeleRing (𝓞 K) K)ˣ} (hΩ : IsFundamentalDomain (Kx K) Ω ν) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (x : (AdeleRing (𝓞 K) K)ˣ) :
    ν (Ω ∩ band K a b ∩ x • ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) =
      ν (shell K) * ENNReal.ofReal (cst K) * ENNReal.ofReal (Real.log (b / a)) := by
  set n : ℝ := NumberField.TateGlobal.ideleNorm K x with hn
  have hnpos : 0 < n := NumberField.TateGlobal.ideleNorm_pos x
  have hset : Ω ∩ band K a b ∩ x • ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) =
      x • ((x⁻¹ • Ω) ∩ band K (a / n) (b / n) ∩
        ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) := by
    rw [Set.smul_set_inter, Set.smul_set_inter, smul_inv_smul, hn, smul_band]
  rw [hset, measure_smul]
  have hΩ' : IsFundamentalDomain (Kx K) (x⁻¹ • Ω) ν := hΩ.smul_of_comm x⁻¹
  rw [measure_inter_band_inter_H ν hreg hΩ' (a / n) (b / n) (div_pos ha hnpos)
    (div_le_div_of_nonneg_right hab hnpos.le), div_div_div_cancel_right₀ hnpos.ne']

theorem measure_inter_band (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [hν : ν.IsHaarMeasure]
    (hreg : ∀ F : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain (E K) F (ν.restrict ((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν (((U K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩ band K a b) =
          ν (shell K) * ENNReal.ofReal (cst K) * ENNReal.ofReal (Real.log (b / a)))
    (hidx : (H K).index = NumberField.classNumber K)
    {Ω : Set (AdeleRing (𝓞 K) K)ˣ} (hΩ : IsFundamentalDomain (Kx K) Ω ν) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ν (Ω ∩ band K a b) =
      (NumberField.classNumber K : ℝ≥0∞) *
        (ν (shell K) * ENNReal.ofReal (cst K) * ENNReal.ofReal (Real.log (b / a))) := by

  set Q := (AdeleRing (𝓞 K) K)ˣ ⧸ H K
  have hcard : Nat.card Q = NumberField.classNumber K := by rw [← hidx, Subgroup.index_eq_card]
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (NumberField.classNumber_pos K).ne')
  letI : Fintype Q := Fintype.ofFinite Q

  let P : Q → Set (AdeleRing (𝓞 K) K)ˣ := fun q =>
    q.out • ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)
  have hP : ∀ (q : Q) (y : (AdeleRing (𝓞 K) K)ˣ), y ∈ P q ↔ (QuotientGroup.mk y : Q) = q := by
    intro q y
    show y ∈ q.out • ((H K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ↔ _
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe, ← QuotientGroup.eq,
      QuotientGroup.out_eq']
    exact eq_comm
  have hcover : Ω ∩ band K a b = ⋃ q : Q, (Ω ∩ band K a b ∩ P q) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      exact ⟨QuotientGroup.mk y, hy, (hP _ y).2 rfl⟩
    · rintro ⟨q, hy, -⟩
      exact hy
  have hdisj : Pairwise fun q q' : Q => Disjoint (P q) (P q') := by
    intro q q' hqq'
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hqq' (((hP q y).1 hy).symm.trans ((hP q' y).1 hy'))
  rw [hcover, measure_iUnion₀]
  · have hq : ∀ q : Q, ν (Ω ∩ band K a b ∩ P q) =
        ν (shell K) * ENNReal.ofReal (cst K) * ENNReal.ofReal (Real.log (b / a)) := fun q =>
      measure_inter_band_inter_smul_H ν hreg hΩ a b ha hab q.out
    simp_rw [hq]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]
  · exact fun q q' h => Disjoint.aedisjoint (((hdisj h).mono (fun y hy => hy.2) fun y hy => hy.2))
  · intro q
    exact (hΩ.nullMeasurableSet.inter (measurableSet_band K a b).nullMeasurableSet).inter
      ((measurableSet_H K).const_smul _).nullMeasurableSet

end Main

end NumberField.TateGlobal.ClassNumberVolumeReduce
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField.TateGlobal.ClassNumberVolumeReduce"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div.NumberField.TateGlobal.ClassNumberVolumeReduce"

open NumberField.TateGlobal.ClassNumberVolumeReduce in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} ≠ 0 ∧
    ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} ≠ ⊤ ∧
    ∀ Ω : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω ν →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν (Ω ∩ {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}) =
          ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} *
            ENNReal.ofReal ((NumberField.classNumber K : ℝ) * NumberField.Units.regulator K /
              (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) *
            ENNReal.ofReal (Real.log (b / a)) := by
  haveI := hν
  obtain ⟨h0, hT, hreg⟩ :=
    NumberField.TateGlobal.measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
      K ν hν
  have hidx := NumberField.TateGlobal.index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber K
  refine ⟨h0, hT, fun Ω hΩ a b ha hab => ?_⟩
  have hmain := measure_inter_band (K := K) ν hreg hidx hΩ a b ha hab
  rw [show Ω ∩ {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b} = Ω ∩ band K a b from rfl, hmain]
  have hc : ENNReal.ofReal ((NumberField.classNumber K : ℝ) * NumberField.Units.regulator K /
      (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) =
      (NumberField.classNumber K : ℝ≥0∞) * ENNReal.ofReal (cst K) := by
    rw [mul_div_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    rfl
  rw [hc]
  show _ = ν (shell K) * _ * _
  ring

end S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div
end P2MW
export P2MW.S_NumberField_TateGlobal_measure_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_classNumber_mul_regulator_div (solution)
