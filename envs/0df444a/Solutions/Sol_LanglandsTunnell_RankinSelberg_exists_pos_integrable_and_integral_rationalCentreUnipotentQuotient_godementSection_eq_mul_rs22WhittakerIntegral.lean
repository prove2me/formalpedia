-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/43d34318-34c1-5549-8997-d819a427e9d8

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_LanglandsTunnell_RankinSelberg_mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral
import Theorems.Thm_MeasureTheory_lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one
import Theorems.Thm_MeasureTheory_integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_lintegral_adelicUnipotent_lintegral_indicator_slab_mul_density_centralScalar_inv_mul_eq
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isClosed_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar
import Theorems.Thm_AutomorphicForm_isClosed_adelicUnipotent
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.whittakerCoefficient_zero"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain NumberField.TateGlobal
open AutomorphicForm LanglandsTunnell.RankinSelberg
open scoped ENNReal

noncomputable section

namespace Ws1
namespace V2Asm

open HaarQuotient

section GenericFurniture

private theorem sigmaCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : SigmaCompactSpace H :=
  hH.sigmaCompactSpace

private theorem sfinite_of_isHaarMeasure {H : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H]
    [MeasurableSpace H] (ν : Measure H) [ν.IsHaarMeasure] : SFinite ν :=
  inferInstance

section Unipotent

variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]

omit [TopologicalSpace R] [T2Space R] in

private theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | Units.val g 0 0 = 1 ∧ Units.val g 1 0 = 0 ∧ Units.val g 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change Units.val (unipotentGL2 y.toAdd) 0 0 = 1 ∧ Units.val (unipotentGL2 y.toAdd) 1 0 = 0 ∧
      Units.val (unipotentGL2 y.toAdd) 1 1 = 1
    simp [unipotentGL2]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (Units.val g 0 1), ?_⟩
    change unipotentGL2 (Units.val g 0 1) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : Continuous fun g : GL (Fin 2) R => Units.val g := Units.continuous_val
  exact (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))

end Unipotent

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

private theorem measurable_lintegral_weight_mul [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable fun g : G => ∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH := by
  have hm : Measurable fun p : H × G => HaarQuotient.weight H μH ((p.1 : G) * p.2) :=
    (measurable_weight H μH).comp ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  exact hm.lintegral_prod_left

private theorem measurable_density [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] (H : Subgroup G)
    (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  unfold HaarQuotient.density
  exact (measurable_weight H μH).div (measurable_lintegral_weight_mul H μH)

end Density

end GenericFurniture

namespace Unimodular

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

private theorem lintegral_inv_eq_of_comm (hcomm : ∀ a b : K, a * b = b * a) (μ : Measure K) [μ.IsHaarMeasure]
    [μ.Regular] (f : K → ℝ≥0∞) : ∫⁻ n, f n⁻¹ ∂μ = ∫⁻ n, f n ∂μ := by
  letI : CommGroup K := { (inferInstance : Group K) with mul_comm := hcomm }
  haveI : μ.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular μ
  exact lintegral_inv_eq_self f

private theorem lintegral_inv_eq_of_comm' [SecondCountableTopology K] (hcomm : ∀ a b : K, a * b = b * a)
    (μ : Measure K) [μ.IsHaarMeasure] (f : K → ℝ≥0∞) : ∫⁻ n, f n⁻¹ ∂μ = ∫⁻ n, f n ∂μ :=
  lintegral_inv_eq_of_comm hcomm μ f

private theorem subgroup_mul_comm {G : Type*} [Group G] {A : Type*} [CommGroup A] (φ : A →* G)
    (a b : φ.range) : a * b = b * a := by
  obtain ⟨_, x, rfl⟩ := a
  obtain ⟨_, y, rfl⟩ := b
  ext
  simp only [Subgroup.coe_mul, ← map_mul, mul_comm]

end Unimodular

namespace Abelian

private theorem isMulRightInvariant_of_comm {H : Type*} [Group H] [MeasurableSpace H] (μ : Measure H)
    [μ.IsMulLeftInvariant] (hcomm : ∀ a b : H, a * b = b * a) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (fun x : H => x * g) = fun x : H => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g

private theorem range_mul_comm {M G : Type*} [CommGroup M] [Group G] (φ : M →* G) (a b : φ.range) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

private theorem subgroupOf_mul_comm {G : Type*} [Group G] (H K : Subgroup G) (hcomm : ∀ a b : H, a * b = b * a)
    (a b : H.subgroupOf K) : a * b = b * a := by
  apply Subtype.ext
  apply Subtype.ext
  have ha : ((a : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp a.2
  have hb : ((b : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp b.2
  have := congrArg Subtype.val (hcomm ⟨_, ha⟩ ⟨_, hb⟩)
  simpa using this

end Abelian

namespace DensNorm

open scoped Pointwise

section Norm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SigmaCompactSpace G] [WeaklyLocallyCompactSpace G]
  (H : Subgroup G) (μH : Measure H)

private def coeff (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem weight_eq (g : G) :
    weight H μH g = ∑' n : ℕ,
      coeff H μH n * (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  unfold HaarQuotient.weight
  rw [dif_pos ⟨inferInstance, inferInstance⟩]
  rfl

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem coeff_le (n : ℕ) : coeff H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n :=
  mul_le_of_le_one_right (by simp) (ENNReal.inv_le_one.mpr le_self_add)

private theorem lintegral_term_le [μH.IsMulRightInvariant] (n : ℕ) (g : G) :
    ∫⁻ x : H, coeff H μH n *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) ∂μH ≤
      (2⁻¹ : ℝ≥0∞) ^ n := by
  set E : Set G := CompactExhaustion.choice G (n + 1) with hE
  set U : Set H := {x : H | (x : G) * g ∈ interior E} with hU
  have hUmeas : MeasurableSet U :=
    (isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)).measurableSet
  have hfun : (fun x : H => coeff H μH n * (interior E).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g)) =
      fun x : H => U.indicator (fun _ => coeff H μH n) x := by
    funext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (show (x : G) * g ∈ interior E from hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (x : G) * g ∉ interior E from hx)]
  rw [hfun, lintegral_indicator_const hUmeas]

  by_cases hne : U = ∅
  · simp [hne]
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hsub : U ⊆ (fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by
    intro x hx
    refine ⟨(x : G) * g, interior_subset hx, ((x₀ : G) * g)⁻¹, Set.inv_mem_inv.mpr (interior_subset hx₀), ?_⟩
    simp [mul_assoc]
  calc coeff H μH n * μH U ≤ coeff H μH n * μH ((fun x : H => x * x₀⁻¹) ⁻¹' (((↑) : H → G) ⁻¹' (E * E⁻¹))) :=
        mul_le_mul_right (measure_mono hsub) _
    _ = coeff H μH n * μH (((↑) : H → G) ⁻¹' (E * E⁻¹)) := by rw [measure_preimage_mul_right]
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
        unfold coeff
        rw [mul_assoc]
        refine mul_le_of_le_one_right (by simp) ?_
        rw [← hE, ← ENNReal.div_eq_inv_mul]
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)

private theorem measurable_term (n : ℕ) (g : G) :
    Measurable fun x : H => coeff H μH n *
      (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) :=
  measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet).comp
    (measurable_subtype_coe.mul_const g))

private theorem lintegral_weight_mul_ne_top [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ ⊤ := by
  simp_rw [weight_eq H μH]
  rw [lintegral_tsum fun n => (measurable_term H μH n g).aemeasurable]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n => lintegral_term_le H μH n g)
  rw [ENNReal.tsum_geometric]
  simp

private theorem lintegral_weight_mul_ne_zero [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) :
    ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH ≠ 0 := by
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice G).exists_mem g
  have hg : g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) :=
    (CompactExhaustion.choice G).subset_interior_succ n hn
  set U : Set H := {x : H | (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)} with hU
  have hUopen : IsOpen U := isOpen_interior.preimage (continuous_subtype_val.mul continuous_const)
  have hU1 : (1 : H) ∈ U := by
    show ((1 : H) : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G)
    simpa using hg

  have hcompact : IsCompact (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)) :=
    (hH.isClosedEmbedding_subtypeVal).isCompact_preimage
      (((CompactExhaustion.choice G).isCompact (n + 1)).mul ((CompactExhaustion.choice G).isCompact (n + 1)).inv)
  have hcoeff : coeff H μH n ≠ 0 := by
    unfold coeff
    refine mul_ne_zero (pow_ne_zero _ (by simp)) (ENNReal.inv_ne_zero.mpr ?_)
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hcompact.measure_lt_top.ne⟩

  have hterm : coeff H μH n * μH U ≤ ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH := by
    rw [← lintegral_indicator_const hUopen.measurableSet]
    refine lintegral_mono fun x => ?_
    rw [weight_eq H μH]
    refine le_trans ?_ (ENNReal.le_tsum n)
    by_cases hx : x ∈ U
    · have hxg : (x : G) * g ∈ interior (CompactExhaustion.choice G (n + 1) : Set G) := hx
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxg]
    · simp [Set.indicator_of_notMem hx]
  refine ne_of_gt (lt_of_lt_of_le ?_ hterm)
  exact ENNReal.mul_pos hcoeff (hUopen.measure_pos μH ⟨1, hU1⟩).ne'

omit [IsTopologicalGroup G] [BorelSpace G] in

private theorem weight_ne_top (g : G) : weight H μH g ≠ ⊤ := by
  rw [weight_eq]
  refine ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ?_ ?_
  · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
    exact ENNReal.inv_ne_top.mpr (by simp)
  · refine ENNReal.tsum_le_tsum fun n => ?_
    refine le_trans (mul_le_of_le_one_right (by simp) ?_) (coeff_le H μH n)
    exact Set.indicator_le_self' (fun _ _ => zero_le_one) g |>.trans le_rfl

private theorem density_ne_top [μH.IsHaarMeasure] (hH : IsClosed (H : Set G)) (g : G) : density H μH g ≠ ⊤ :=
  ENNReal.div_ne_top (weight_ne_top H μH g) (lintegral_weight_mul_ne_zero H μH hH g)

end Norm

end DensNorm

section Instances

variable (F : Type) [Field F] [NumberField F]

theorem secondCountableTopology_units : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem secondCountableTopology_gl : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

end Instances

section Algebra

variable (F : Type) [Field F] [NumberField F]

theorem centralScalar_coe (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      (z : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom z : (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ˣ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = _
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        (z : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      Units.continuous_val.smul continuous_const
    exact h1.congr fun z => (centralScalar_coe F z).symm
  · have h1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      (Units.continuous_val.comp continuous_inv).smul continuous_const
    refine h1.congr fun z => ?_
    show _ = ((↑(centralScalar (𝓞 F) F z)⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
    rw [← map_inv]
    exact (centralScalar_coe F z⁻¹).symm

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_coe, smul_one_mul, Matrix.mul_smul, mul_one]

theorem det_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z * z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, centralScalar_coe, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin, Units.val_mul, pow_two]

theorem globalPoints_scalar_eq_centralScalar (a : Fˣ) :
    globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) =
      centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) := by
  apply Units.ext
  rw [centralScalar_coe]
  ext i j
  change algebraMap F (AdeleRing (𝓞 F) F) ((Matrix.scalar (Fin 2) (a : F)) i j) = _
  rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 F) F => ((g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det)
  · have : (fun g : AdelicGL2 (𝓞 F) F => ((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ).val) =
        fun g => ((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem bottomRowVec_unipotent_mul (n : adelicUnipotent F) (g : AdelicGL2 (𝓞 F) F) (t : AdeleRing (𝓞 F) F) :
    bottomRowVec F ((n : AdelicGL2 (𝓞 F) F) * g) t = bottomRowVec F g t := by
  obtain ⟨y, hy⟩ := n.2
  funext j
  simp only [bottomRowVec, Units.val_mul, ← hy]
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [unipotentGL2Hom, unipotentGL2]

theorem det_unipotent (n : adelicUnipotent F) :
    Matrix.GeneralLinearGroup.det (n : AdelicGL2 (𝓞 F) F) = 1 := by
  obtain ⟨y, hy⟩ := n.2
  apply Units.ext
  rw [← hy]
  simp [unipotentGL2Hom, unipotentGL2, Matrix.det_fin_two]

theorem bottomRowVec_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) (t : AdeleRing (𝓞 F) F) :
    bottomRowVec F (centralScalar (𝓞 F) F z * g) t = bottomRowVec F g (t * z) := by
  funext j
  simp only [bottomRowVec, Units.val_mul, centralScalar_coe, smul_one_mul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem unipotent_mul_comm (a b : adelicUnipotent F) : a * b = b * a :=
  Abelian.range_mul_comm _ a b

def slab (e₁ e₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {x | ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc e₁ e₂}

theorem measurableSet_slab (e₁ e₂ : ℝ) : MeasurableSet (slab F e₁ e₂) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F e₁ e₂

theorem unipotent_mul_mem_slab_iff {e₁ e₂ : ℝ} (n : adelicUnipotent F) (g : AdelicGL2 (𝓞 F) F) :
    (n : AdelicGL2 (𝓞 F) F) * g ∈ slab F e₁ e₂ ↔ g ∈ slab F e₁ e₂ := by
  simp only [slab, Set.mem_setOf_eq, map_mul, det_unipotent, one_mul]

theorem principal_mul_mem_slab_iff {e₁ e₂ : ℝ} (a : Fˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) * g ∈
        slab F e₁ e₂ ↔ g ∈ slab F e₁ e₂ := by
  have h1 : ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
    rw [RingHom.toMonoidHom_eq_coe] at h
    simp [ideleNorm, h]
  simp only [slab, Set.mem_setOf_eq, map_mul, det_centralScalar, ideleNorm_mul, h1, one_mul]

end Algebra

end Ws1.V2Asm

namespace Ws1
namespace V2Asm

open HaarQuotient

section Quotient

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  (μ : Measure G) (H : Subgroup G) (μH : Measure H)

theorem comp_out_mk {β : Type*} (f : G → β) (hfH : ∀ (h : H) (g : G), f ((h : G) * g) = f g) :
    (fun q : MulAction.orbitRel.Quotient H G => f q.out) ∘ Quotient.mk'' = f := by
  funext g
  simp only [Function.comp_apply]
  have hrel : MulAction.orbitRel H G ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
    Quotient.mk_out g
  obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.mp hrel
  rw [← hh]
  exact hfH h g

theorem measurable_comp_out {β : Type*} [MeasurableSpace β] (f : G → β) (hf : Measurable f)
    (hfH : ∀ (h : H) (g : G), f ((h : G) * g) = f g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => f q.out := by
  rw [measurable_from_quotient, comp_out_mk H f hfH]
  exact hf

theorem integral_quotient_eq (f : G → ℂ) (hf : Measurable f) (hfH : ∀ (h : H) (g : G), f ((h : G) * g) = f g) :
    ∫ q, f q.out ∂(HaarQuotient.measure μ H μH) = ∫ g, f g ∂(μ.withDensity (density H μH)) ∧
    (Integrable (fun q : MulAction.orbitRel.Quotient H G => f q.out) (HaarQuotient.measure μ H μH) ↔
      Integrable f (μ.withDensity (density H μH))) := by
  have hm := measurable_comp_out H f hf hfH
  have hc := comp_out_mk H f hfH
  unfold HaarQuotient.measure
  refine ⟨?_, ?_⟩
  · rw [integral_map measurable_quotient_mk''.aemeasurable hm.aestronglyMeasurable]
    exact congrArg (fun F : G → ℂ => ∫ g, F g ∂(μ.withDensity (density H μH))) hc
  · rw [integrable_map_measure hm.aestronglyMeasurable measurable_quotient_mk''.aemeasurable, hc]

theorem lintegral_quotient_eq (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ (h : H) (g : G), f ((h : G) * g) = f g) :
    ∫⁻ q, f q.out ∂(HaarQuotient.measure μ H μH) = ∫⁻ g, f g ∂(μ.withDensity (density H μH)) := by
  have hm := measurable_comp_out H f hf hfH
  have hc := comp_out_mk H f hfH
  unfold HaarQuotient.measure
  rw [lintegral_map hm measurable_quotient_mk'']
  exact congrArg (fun F : G → ℝ≥0∞ => ∫⁻ g, F g ∂(μ.withDensity (density H μH))) hc

end Quotient

section Main

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

local notation "Gp" => AdelicGL2 (𝓞 F) F
local notation "μG" => adelicGLHaar (Fin 2) (𝓞 F) F
local notation "zc" => centralScalar (𝓞 F) F

theorem measurable_rs22Kernel (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦm : Measurable Φ) (s : ℂ) :
    Measurable (rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  unfold rs22Kernel
  have h1 : Measurable fun g : Gp => ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
    (hμc.comp (continuous_det F)).measurable
  have h2 : Measurable fun g : Gp =>
      ((cpowChar (moduleChar F) (moduleChar_pos F) (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
    have hc : Continuous fun g : Gp => ((ideleNorm F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm_det F)
    have : (fun g : Gp =>
        ((cpowChar (moduleChar F) (moduleChar_pos F) (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) =
        fun g => ((ideleNorm F (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s + 1 / 2) := by
      funext g; rw [cpowChar_apply_val]; rfl
    rw [this]
    exact (hc.measurable.pow_const _)
  have h3 : Measurable fun g : Gp => Φ (bottomRowVec F g 1) := by
    refine hΦm.comp ?_
    refine (continuous_pi fun j => ?_).measurable
    exact continuous_const.mul ((Units.continuous_val.matrix_elem 1 j))
  exact (h1.mul h2).mul h3

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in

theorem rs22Kernel_unipotent_mul (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (n : adelicUnipotent F) (g : Gp) :
    rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s ((n : Gp) * g) =
      rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s g := by
  unfold rs22Kernel
  rw [map_mul, det_unipotent, one_mul, bottomRowVec_unipotent_mul]

variable (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]

theorem lintegral_mul_lintegral_centre_eq (ρ φ : Gp → ℝ≥0∞) (hρ : Measurable ρ) (hφ : Measurable φ) :
    ∫⁻ g, ρ g * (∫⁻ t, φ (zc t * g) ∂ν₀) ∂μG = ∫⁻ g, φ g * (∫⁻ t, ρ ((zc t)⁻¹ * g) ∂ν₀) ∂μG := by
  haveI := secondCountableTopology_units F
  haveI := secondCountableTopology_gl F
  haveI : (μG).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hz : Measurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => zc p.2 * p.1 :=
    ((continuous_centralScalar F).measurable.comp measurable_snd).mul measurable_fst
  have hzi : Measurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => (zc p.2)⁻¹ * p.1 :=
    ((continuous_centralScalar F).measurable.comp measurable_snd).inv.mul measurable_fst
  have hA : Measurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => ρ p.1 * φ (zc p.2 * p.1) :=
    (hρ.comp measurable_fst).mul (hφ.comp hz)
  have hB : Measurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => φ p.1 * ρ ((zc p.2)⁻¹ * p.1) :=
    (hφ.comp measurable_fst).mul (hρ.comp hzi)
  calc ∫⁻ g, ρ g * (∫⁻ t, φ (zc t * g) ∂ν₀) ∂μG
      = ∫⁻ g, ∫⁻ t, ρ g * φ (zc t * g) ∂ν₀ ∂μG := by
        refine lintegral_congr fun g => ?_
        exact (lintegral_const_mul (ρ g) (show Measurable (fun t => φ (zc t * g)) from
          hφ.comp ((continuous_centralScalar F).measurable.mul_const g))).symm
    _ = ∫⁻ t, ∫⁻ g, ρ g * φ (zc t * g) ∂μG ∂ν₀ := lintegral_lintegral_swap hA.aemeasurable
    _ = ∫⁻ t, ∫⁻ g, φ g * ρ ((zc t)⁻¹ * g) ∂μG ∂ν₀ := by
        refine lintegral_congr fun t => ?_
        have h := lintegral_mul_left_eq_self (μ := μG) (fun g => φ g * ρ ((zc t)⁻¹ * g)) (zc t)
        simp only [inv_mul_cancel_left] at h
        rw [← h]
        refine lintegral_congr fun g => ?_
        ring
    _ = ∫⁻ g, ∫⁻ t, φ g * ρ ((zc t)⁻¹ * g) ∂ν₀ ∂μG := (lintegral_lintegral_swap hB.aemeasurable).symm
    _ = ∫⁻ g, φ g * (∫⁻ t, ρ ((zc t)⁻¹ * g) ∂ν₀) ∂μG := by
        refine lintegral_congr fun g => ?_
        exact lintegral_const_mul (φ g) (show Measurable (fun t => ρ ((zc t)⁻¹ * g)) from
          hρ.comp ((continuous_centralScalar F).measurable.inv.mul_const g))

end Main

end Ws1.V2Asm

namespace Ws1
namespace V2Asm

open HaarQuotient

section Final

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)

local notation "Gp" => AdelicGL2 (𝓞 F) F
local notation "μG" => adelicGLHaar (Fin 2) (𝓞 F) F
local notation "zc" => centralScalar (𝓞 F) F
local notation "ρN" => density (adelicUnipotent F) (unipotentHaar F)
local notation "ρZN" => density (rationalCentreUnipotent F) (rationalCentreUnipotentHaar F)

def Psi (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) (W W' : Gp → ℂ) :
    Gp → ℂ :=
  fun g => W g * W' g * rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s g

def Icen (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) (W W' : Gp → ℂ) :
    Gp → ℂ :=
  fun g => ∫ t, Psi F μ Φ s W W' (zc t * g) ∂ν₀

def Theta (e₁ e₂ : ℝ) (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (W W' : Gp → ℂ) : Gp → ℂ :=
  fun g => (slab F e₁ e₂).indicator (fun _ => (1 : ℂ)) g * Icen F ν₀ μ Φ s W W' g

def Lam (e₁ e₂ : ℝ) : Gp → ℝ≥0∞ :=
  fun y => ∫⁻ t, (slab F e₁ e₂).indicator ρZN ((zc t)⁻¹ * y) ∂ν₀

variable [ν₀.IsHaarMeasure]

theorem main
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (μ ν ω ω' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hωμν : ω * ω' * μ * ν = 1)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦm : Measurable Φ)
      (s : ℂ)
      (W W' : AdelicGL2 (𝓞 F) F → ℂ) (_hWm : Measurable W) (_hW'm : Measurable W')
      (_hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        W (centralScalar (𝓞 F) F z * g) * W' (centralScalar (𝓞 F) F z * g) =
          ((ω z : ℂˣ) : ℂ) * ((ω' z : ℂˣ) : ℂ) * (W g * W' g))
      (_hN : ∀ (n : adelicUnipotent F) (g : AdelicGL2 (𝓞 F) F),
        W ((n : AdelicGL2 (𝓞 F) F) * g) * W' ((n : AdelicGL2 (𝓞 F) F) * g) = W g * W' g)
      (_hunf : Integrable (fun q : UnipotentQuotient F =>
          ‖W q.out * W' q.out * rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s q.out‖)
        (unipotentQuotientMeasure F)),
      Integrable (fun q : RationalCentreUnipotentQuotient F =>
          ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}.indicator
              (fun _ => (1 : ℂ)) q.out) *
            (W q.out * W' q.out) *
            godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s q.out)
        (rationalCentreUnipotentQuotientMeasure F) ∧
      ∫ q : RationalCentreUnipotentQuotient F,
          ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}.indicator
              (fun _ => (1 : ℂ)) q.out) *
            (W q.out * W' q.out) *
            godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s q.out
          ∂(rationalCentreUnipotentQuotientMeasure F) =
        (C : ℂ) * rs22WhittakerIntegral F W W' μ (moduleChar F) (moduleChar_pos F) Φ s := by
  classical

  haveI : LocallyCompactSpace (AdeleRing (𝓞 F) F)ˣ := inferInstance
  haveI := secondCountableTopology_units F
  haveI := secondCountableTopology_gl F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI hμG : (μG).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨hμN, hμNr⟩ := AutomorphicForm.isHaarMeasure_and_isMulRightInvariant_unipotentHaar F
  obtain ⟨hμZN, hμZNr⟩ := AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant F
  haveI := hμN; haveI := hμNr; haveI := hμZN; haveI := hμZNr
  have hNc := AutomorphicForm.isClosed_adelicUnipotent F
  have hZNc := AutomorphicForm.isClosed_rationalCentreUnipotent F
  haveI : LocallyCompactSpace (adelicUnipotent F) := hNc.locallyCompactSpace
  haveI : LocallyCompactSpace (rationalCentreUnipotent F) := hZNc.locallyCompactSpace
  haveI : SecondCountableTopology (adelicUnipotent F) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SecondCountableTopology (rationalCentreUnipotent F) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := inferInstance
  haveI : SigmaCompactSpace Gp := inferInstance
  haveI : SigmaCompactSpace (adelicUnipotent F) := inferInstance
  haveI : SigmaCompactSpace (rationalCentreUnipotent F) := inferInstance
  haveI : SFinite ν₀ := sfinite_of_isHaarMeasure ν₀
  haveI : SFinite μG := sfinite_of_isHaarMeasure _
  haveI : SFinite (unipotentHaar F) := sfinite_of_isHaarMeasure _
  haveI : SFinite (rationalCentreUnipotentHaar F) := sfinite_of_isHaarMeasure _

  obtain ⟨C, hC, hCavg⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_forall_lintegral_adelicUnipotent_lintegral_indicator_slab_mul_density_centralScalar_inv_mul_eq
      F ν₀ e₁ e₂ he₁ he
  refine ⟨C, hC, ?_⟩
  intro μ ν ω ω' hωμν hμc hνc Φ hΦm s W W' hWm hW'm hZ hN hunf
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hCt : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top

  have hρNm : Measurable ρN := measurable_density _ _
  have hρZNm : Measurable ρZN := measurable_density _ _
  have hρNt : ∀ g : Gp, ρN g ≠ ⊤ := fun g => DensNorm.density_ne_top _ _ hNc g
  have hρZNt : ∀ g : Gp, ρZN g ≠ ⊤ := fun g => DensNorm.density_ne_top _ _ hZNc g
  have hρN1 : ∀ g : Gp, ∫⁻ n : adelicUnipotent F, ρN ((n : Gp) * g) ∂(unipotentHaar F) = 1 := fun g =>
    HaarQuotient.lintegral_density_mul_eq_one _ hNc _ g
  have hinvN : ∀ f : adelicUnipotent F → ℝ≥0∞, ∫⁻ n, f n⁻¹ ∂(unipotentHaar F) = ∫⁻ n, f n ∂(unipotentHaar F) :=
    Unimodular.lintegral_inv_eq_of_comm' (unipotent_mul_comm F) _

  have hSm : MeasurableSet (slab F e₁ e₂) := measurableSet_slab F e₁ e₂
  have hSρm : Measurable ((slab F e₁ e₂).indicator ρZN) := hρZNm.indicator hSm
  have hSρt : ∀ g : Gp, (slab F e₁ e₂).indicator ρZN g ≠ ⊤ := fun g => by
    by_cases hg : g ∈ slab F e₁ e₂
    · rw [Set.indicator_of_mem hg]; exact hρZNt g
    · rw [Set.indicator_of_notMem hg]; exact ENNReal.zero_ne_top

  have hΨm : Measurable (Psi F μ Φ s W W') :=
    (hWm.mul hW'm).mul (measurable_rs22Kernel F μ hμc Φ hΦm s)
  have hΨN : ∀ (n : adelicUnipotent F) (g : Gp), Psi F μ Φ s W W' ((n : Gp) * g) = Psi F μ Φ s W W' g := by
    intro n g
    simp only [Psi, hN n g, rs22Kernel_unipotent_mul]
  have hz : Measurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => zc p.2 * p.1 :=
    ((continuous_centralScalar F).measurable.comp measurable_snd).mul measurable_fst
  have hzi : Measurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => (zc p.2)⁻¹ * p.1 :=
    ((continuous_centralScalar F).measurable.comp measurable_snd).inv.mul measurable_fst

  have hIm : Measurable (Icen F ν₀ μ Φ s W W') := by
    have h : StronglyMeasurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => Psi F μ Φ s W W' (zc p.2 * p.1) :=
      (hΨm.comp hz).stronglyMeasurable
    exact h.integral_prod_right'.measurable
  have hGC : ∀ g : Gp, W g * W' g * godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s g =
      Icen F ν₀ μ Φ s W W' g := fun g =>
    (LanglandsTunnell.RankinSelberg.mul_mul_rs22Kernel_centralScalar_mul_eq_and_mul_godementSection_eq_integral
      F ν₀ μ ν ω ω' hωμν Φ s W W' hZ g).2
  have hΘm : Measurable (Theta F ν₀ e₁ e₂ μ Φ s W W') :=
    (measurable_const.indicator hSm).mul hIm

  have hIcN : ∀ (n : adelicUnipotent F) (g : Gp), Icen F ν₀ μ Φ s W W' ((n : Gp) * g) = Icen F ν₀ μ Φ s W W' g := by
    intro n g
    simp only [Icen]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show Psi F μ Φ s W W' (zc t * ((n : Gp) * g)) = Psi F μ Φ s W W' (zc t * g)
    rw [← mul_assoc, centralScalar_mul_comm F t, mul_assoc, hΨN]
  have hIcZ : ∀ (a : Fˣ) (g : Gp),
      Icen F ν₀ μ Φ s W W' (zc (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) * g) =
        Icen F ν₀ μ Φ s W W' g := by
    intro a g
    simp only [Icen]
    set p := Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a
    have h := integral_mul_left_eq_self (μ := ν₀) (fun t => Psi F μ Φ s W W' (zc t * g)) p
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show Psi F μ Φ s W W' (zc t * (zc p * g)) = Psi F μ Φ s W W' (zc (p * t) * g)
    rw [← mul_assoc, ← map_mul, mul_comm t p]
  have hΘinv : ∀ (h : rationalCentreUnipotent F) (g : Gp),
      Theta F ν₀ e₁ e₂ μ Φ s W W' ((h : Gp) * g) = Theta F ν₀ e₁ e₂ μ Φ s W W' g := by
    intro h
    have hmem : (h : Gp) ∈ Subgroup.closure ((rationalCentre F : Set Gp) ∪ (adelicUnipotent F : Set Gp)) := by
      rw [← Subgroup.sup_eq_closure]; exact h.2
    refine Subgroup.closure_induction (p := fun x _ => ∀ g : Gp,
        Theta F ν₀ e₁ e₂ μ Φ s W W' (x * g) = Theta F ν₀ e₁ e₂ μ Φ s W W' g) ?_ ?_ ?_ ?_ hmem
    · rintro x (⟨a, rfl⟩ | hx) g
      · show Theta F ν₀ e₁ e₂ μ Φ s W W'
            (globalPoints (𝓞 F) F (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a) * g) = _
        rw [globalPoints_scalar_eq_centralScalar]
        simp only [Theta, Set.indicator_apply, principal_mul_mem_slab_iff, hIcZ]
      · simp only [Theta, Set.indicator_apply, unipotent_mul_mem_slab_iff F ⟨x, hx⟩, hIcN ⟨x, hx⟩]
    · intro g; rw [one_mul]
    · intro x y _ _ hx hy g
      rw [mul_assoc, hx, hy]
    · intro x _ hx g
      have := hx (x⁻¹ * g)
      rw [mul_inv_cancel_left] at this
      exact this.symm

  have hL := integral_quotient_eq μG (rationalCentreUnipotent F) (rationalCentreUnipotentHaar F)
    (Theta F ν₀ e₁ e₂ μ Φ s W W') hΘm hΘinv
  have hR := integral_quotient_eq μG (adelicUnipotent F) (unipotentHaar F) (Psi F μ Φ s W W') hΨm hΨN
  have hRn := integral_quotient_eq μG (adelicUnipotent F) (unipotentHaar F)
    (fun g => ((‖Psi F μ Φ s W W' g‖ : ℝ) : ℂ)) (Complex.measurable_ofReal.comp hΨm.norm)
    (fun n g => by simp only [hΨN])

  have hunf' : Integrable (fun q : UnipotentQuotient F => ((‖Psi F μ Φ s W W' q.out‖ : ℝ) : ℂ))
      (unipotentQuotientMeasure F) := by
    have := hunf.ofReal (𝕜 := ℂ)
    exact this
  have hΨi : Integrable (Psi F μ Φ s W W') ((μG).withDensity ρN) := by
    have h1 : Integrable (fun g => ((‖Psi F μ Φ s W W' g‖ : ℝ) : ℂ)) ((μG).withDensity ρN) := hRn.2.mp hunf'
    have h2 : Integrable (fun g => ‖Psi F μ Φ s W W' g‖) ((μG).withDensity ρN) := by
      refine (h1.norm).congr (Filter.Eventually.of_forall fun g => ?_)
      simp only [Complex.norm_real, norm_norm]
    exact (integrable_norm_iff hΨm.aestronglyMeasurable).mp h2
  have hK : ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * ρN g ∂μG < ⊤ := by
    have h := hΨi.2
    unfold HasFiniteIntegral at h
    rw [lintegral_withDensity_eq_lintegral_mul _ hρNm hΨm.enorm] at h
    calc ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * ρN g ∂μG = ∫⁻ g, (ρN * fun g => ‖Psi F μ Φ s W W' g‖ₑ) g ∂μG := by
          refine lintegral_congr fun g => ?_; simp only [Pi.mul_apply]; ring
      _ < ⊤ := h

  have hΛm : Measurable (Lam F ν₀ e₁ e₂) := by
    have h : Measurable fun p : Gp × (AdeleRing (𝓞 F) F)ˣ => (slab F e₁ e₂).indicator ρZN ((zc p.2)⁻¹ * p.1) :=
      hSρm.comp hzi
    exact h.lintegral_prod_right'
  have hΛN : ∀ g : Gp, ∫⁻ n : adelicUnipotent F, Lam F ν₀ e₁ e₂ ((n : Gp) * g) ∂(unipotentHaar F) = ENNReal.ofReal C :=
    fun g => hCavg g
  set Λ' : Gp → ℝ≥0∞ := fun y => (ENNReal.ofReal C)⁻¹ * Lam F ν₀ e₁ e₂ y with hΛ'
  have hΛ'm : Measurable Λ' := hΛm.const_mul _
  have hΛ'1 : ∀ g : Gp, ∫⁻ n : adelicUnipotent F, Λ' ((n : Gp) * g) ∂(unipotentHaar F) = 1 := by
    intro g
    simp only [hΛ']
    rw [lintegral_const_mul _ (show Measurable (fun n : adelicUnipotent F => Lam F ν₀ e₁ e₂ ((n : Gp) * g)) from
      hΛm.comp (measurable_subtype_coe.mul_const g)), hΛN g, ENNReal.inv_mul_cancel hC0 hCt]
  have hΨNe : ∀ (n : adelicUnipotent F) (g : Gp), ‖Psi F μ Φ s W W' ((n : Gp) * g)‖ₑ = ‖Psi F μ Φ s W W' g‖ₑ :=
    fun n g => by rw [hΨN]
  have hKΛ : ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * Lam F ν₀ e₁ e₂ g ∂μG =
      ENNReal.ofReal C * ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * ρN g ∂μG := by
    have hD := MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_lintegral_subgroup_mul_eq_one
      (adelicUnipotent F) μG (unipotentHaar F) hinvN hρNm hΛ'm hρN1 hΛ'1 hΨm.enorm.aemeasurable hΨNe
    rw [hD]
    simp only [hΛ']
    rw [← lintegral_const_mul (ENNReal.ofReal C) (show Measurable (fun g : Gp =>
      ‖Psi F μ Φ s W W' g‖ₑ * ((ENNReal.ofReal C)⁻¹ * Lam F ν₀ e₁ e₂ g)) from hΨm.enorm.mul (hΛm.const_mul _))]
    refine lintegral_congr fun g => ?_
    rw [show ENNReal.ofReal C * (‖Psi F μ Φ s W W' g‖ₑ * ((ENNReal.ofReal C)⁻¹ * Lam F ν₀ e₁ e₂ g)) =
        (ENNReal.ofReal C * (ENNReal.ofReal C)⁻¹) * (‖Psi F μ Φ s W W' g‖ₑ * Lam F ν₀ e₁ e₂ g) by ring,
      ENNReal.mul_inv_cancel hC0 hCt, one_mul]
  have hKΛt : ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * Lam F ν₀ e₁ e₂ g ∂μG < ⊤ := by
    rw [hKΛ]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK

  have hEx : ∫⁻ g, (slab F e₁ e₂).indicator ρZN g * (∫⁻ t, ‖Psi F μ Φ s W W' (zc t * g)‖ₑ ∂ν₀) ∂μG =
      ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * Lam F ν₀ e₁ e₂ g ∂μG :=
    lintegral_mul_lintegral_centre_eq F ν₀ _ _ hSρm hΨm.enorm

  set Λt : Gp → ℝ≥0∞ := fun y => ENNReal.ofReal (Lam F ν₀ e₁ e₂ y).toReal with hΛt
  have hΛtm : Measurable Λt := hΛm.ennreal_toReal.ennreal_ofReal
  have hΛtt : ∀ y, Λt y ≠ ⊤ := fun y => ENNReal.ofReal_ne_top
  have hΛt_toReal : ∀ y, (Λt y).toReal = (Lam F ν₀ e₁ e₂ y).toReal := fun y =>
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg
  have hΛt_eq : ∀ y, Lam F ν₀ e₁ e₂ y ≠ ⊤ → Λt y = Lam F ν₀ e₁ e₂ y := fun y hy => ENNReal.ofReal_toReal hy

  set Λt' : Gp → ℝ≥0∞ := fun y => (ENNReal.ofReal C)⁻¹ * Λt y with hΛt'
  have hΛt'm : Measurable Λt' := hΛtm.const_mul _
  have hΛt't : ∀ y, Λt' y ≠ ⊤ := fun y => ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hC0) (hΛtt y)
  have hΛt'1 : ∀ g : Gp, ∫⁻ n : adelicUnipotent F, Λt' ((n : Gp) * g) ∂(unipotentHaar F) = 1 := by
    intro g
    have hmeas : Measurable fun n : adelicUnipotent F => Lam F ν₀ e₁ e₂ ((n : Gp) * g) :=
      hΛm.comp (measurable_subtype_coe.mul_const g)
    have hae : ∀ᵐ n : adelicUnipotent F ∂(unipotentHaar F), Lam F ν₀ e₁ e₂ ((n : Gp) * g) < ⊤ :=
      ae_lt_top hmeas (by rw [hΛN g]; exact hCt)
    have h1 : ∫⁻ n : adelicUnipotent F, Λt ((n : Gp) * g) ∂(unipotentHaar F) =
        ∫⁻ n : adelicUnipotent F, Lam F ν₀ e₁ e₂ ((n : Gp) * g) ∂(unipotentHaar F) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with n hn
      exact hΛt_eq _ hn.ne
    simp only [hΛt']
    rw [lintegral_const_mul _ (show Measurable (fun n : adelicUnipotent F => Λt ((n : Gp) * g)) from
      hΛtm.comp (measurable_subtype_coe.mul_const g)), h1, hΛN g, ENNReal.inv_mul_cancel hC0 hCt]

  have hΘbound : ∀ g : Gp, ρZN g * ‖Theta F ν₀ e₁ e₂ μ Φ s W W' g‖ₑ ≤
      (slab F e₁ e₂).indicator ρZN g * ∫⁻ t, ‖Psi F μ Φ s W W' (zc t * g)‖ₑ ∂ν₀ := by
    intro g
    by_cases hg : g ∈ slab F e₁ e₂
    · simp only [Theta, Set.indicator_of_mem hg, one_mul]
      exact mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
    · simp only [Theta, Set.indicator_of_notMem hg, zero_mul, enorm_zero, mul_zero, le_refl]
  have hΘi : Integrable (Theta F ν₀ e₁ e₂ μ Φ s W W') ((μG).withDensity ρZN) := by
    refine ⟨hΘm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_withDensity_eq_lintegral_mul _ hρZNm hΘm.enorm]
    calc ∫⁻ g, (ρZN * fun g => ‖Theta F ν₀ e₁ e₂ μ Φ s W W' g‖ₑ) g ∂μG
        ≤ ∫⁻ g, (slab F e₁ e₂).indicator ρZN g * ∫⁻ t, ‖Psi F μ Φ s W W' (zc t * g)‖ₑ ∂ν₀ ∂μG :=
          lintegral_mono fun g => hΘbound g
      _ = ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * Lam F ν₀ e₁ e₂ g ∂μG := hEx
      _ < ⊤ := hKΛt

  set H₁ : Gp × (AdeleRing (𝓞 F) F)ˣ → ℂ :=
    fun p => ((slab F e₁ e₂).indicator ρZN p.1).toReal • Psi F μ Φ s W W' (zc p.2 * p.1) with hH₁
  set H₂ : Gp × (AdeleRing (𝓞 F) F)ˣ → ℂ :=
    fun p => ((slab F e₁ e₂).indicator ρZN ((zc p.2)⁻¹ * p.1)).toReal • Psi F μ Φ s W W' p.1 with hH₂
  have hH₁m : Measurable H₁ := (hSρm.comp measurable_fst).ennreal_toReal.smul (hΨm.comp hz)
  have hH₂m : Measurable H₂ := (hSρm.comp hzi).ennreal_toReal.smul (hΨm.comp measurable_fst)
  have henorm_smul : ∀ (r : ℝ≥0∞) (x : ℂ), r ≠ ⊤ → ‖r.toReal • x‖ₑ = r * ‖x‖ₑ := by
    intro r x hr
    rw [enorm_smul, Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hr]
  have hH₁i : Integrable H₁ ((μG).prod ν₀) := by
    refine ⟨hH₁m.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ hH₁m.enorm.aemeasurable]
    calc ∫⁻ g, ∫⁻ t, ‖H₁ (g, t)‖ₑ ∂ν₀ ∂μG
        = ∫⁻ g, (slab F e₁ e₂).indicator ρZN g * ∫⁻ t, ‖Psi F μ Φ s W W' (zc t * g)‖ₑ ∂ν₀ ∂μG := by
          refine lintegral_congr fun g => ?_
          simp only [hH₁, henorm_smul _ _ (hSρt _)]
          exact lintegral_const_mul _ (show Measurable (fun t => ‖Psi F μ Φ s W W' (zc t * g)‖ₑ) from
            hΨm.enorm.comp ((continuous_centralScalar F).measurable.mul_const g))
      _ = ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * Lam F ν₀ e₁ e₂ g ∂μG := hEx
      _ < ⊤ := hKΛt
  have hH₂i : Integrable H₂ ((μG).prod ν₀) := by
    refine ⟨hH₂m.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [lintegral_prod _ hH₂m.enorm.aemeasurable]
    calc ∫⁻ g, ∫⁻ t, ‖H₂ (g, t)‖ₑ ∂ν₀ ∂μG
        = ∫⁻ g, ‖Psi F μ Φ s W W' g‖ₑ * Lam F ν₀ e₁ e₂ g ∂μG := by
          refine lintegral_congr fun g => ?_
          simp only [hH₂, henorm_smul _ _ (hSρt _), Lam]
          rw [lintegral_mul_const _ (show Measurable (fun t => (slab F e₁ e₂).indicator ρZN ((zc t)⁻¹ * g)) from
            hSρm.comp ((continuous_centralScalar F).measurable.inv.mul_const g)), mul_comm]
      _ < ⊤ := hKΛt

  have hStep1 : ∫ g, Theta F ν₀ e₁ e₂ μ Φ s W W' g ∂((μG).withDensity ρZN) = ∫ g, ∫ t, H₁ (g, t) ∂ν₀ ∂μG := by
    rw [integral_withDensity_eq_integral_toReal_smul hρZNm (Filter.Eventually.of_forall fun g => (hρZNt g).lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show (ρZN g).toReal • Theta F ν₀ e₁ e₂ μ Φ s W W' g = ∫ t, H₁ (g, t) ∂ν₀
    simp only [hH₁, Theta, Icen]
    by_cases hg : g ∈ slab F e₁ e₂
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, one_mul, ← integral_smul]
    · simp [Set.indicator_of_notMem hg]
  have hStep2 : ∫ g, ∫ t, H₁ (g, t) ∂ν₀ ∂μG = ∫ t, ∫ g, H₁ (g, t) ∂μG ∂ν₀ :=
    integral_integral_swap (by simpa only [Function.uncurry_def] using hH₁i)
  have hStep3 : ∀ t, ∫ g, H₁ (g, t) ∂μG = ∫ g, H₂ (g, t) ∂μG := by
    intro t
    have h := integral_mul_left_eq_self (μ := μG) (fun g => H₂ (g, t)) (zc t)
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hH₁, hH₂, inv_mul_cancel_left]
  have hStep4 : ∫ t, ∫ g, H₂ (g, t) ∂μG ∂ν₀ = ∫ g, ∫ t, H₂ (g, t) ∂ν₀ ∂μG :=
    (integral_integral_swap (by simpa only [Function.uncurry_def] using hH₂i)).symm
  have hStep5 : ∀ g : Gp, ∫ t, H₂ (g, t) ∂ν₀ = (Λt g).toReal • Psi F μ Φ s W W' g := by
    intro g
    simp only [hH₂]
    rw [integral_smul_const, hΛt_toReal]
    congr 1
    simp only [Lam]
    exact integral_toReal ((hSρm.comp ((continuous_centralScalar F).measurable.inv.mul_const g)).aemeasurable)
      (Filter.Eventually.of_forall fun t => (hSρt _).lt_top)
  have hStep6 : ∫ g, (Λt g).toReal • Psi F μ Φ s W W' g ∂μG = ∫ g, Psi F μ Φ s W W' g ∂((μG).withDensity Λt) :=
    (integral_withDensity_eq_integral_toReal_smul hΛtm (Filter.Eventually.of_forall fun g => (hΛtt g).lt_top)
      (Psi F μ Φ s W W')).symm

  have hDens := MeasureTheory.integrable_and_integral_withDensity_eq_of_forall_lintegral_subgroup_mul_eq_one
    (adelicUnipotent F) μG (unipotentHaar F) hinvN hρNm hΛt'm hρN1 hΛt'1 hρNt hΛt't hΨN hΨi
  have hΛtC : Λt = (ENNReal.ofReal C) • Λt' := by
    funext y
    simp only [hΛt', Pi.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hC0 hCt, one_mul]
  have hStep7 : ∫ g, Psi F μ Φ s W W' g ∂((μG).withDensity Λt) =
      (C : ℂ) * ∫ g, Psi F μ Φ s W W' g ∂((μG).withDensity ρN) := by
    rw [hΛtC, withDensity_smul _ hΛt'm, integral_smul_measure, hDens.2, ENNReal.toReal_ofReal hC.le,
      Complex.real_smul]

  have hint : (fun q : RationalCentreUnipotentQuotient F =>
      ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}.indicator
          (fun _ => (1 : ℂ)) q.out) *
        (W q.out * W' q.out) *
        godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s q.out) =
      fun q => Theta F ν₀ e₁ e₂ μ Φ s W W' q.out := by
    funext q
    simp only [Theta, mul_assoc]
    rw [← mul_assoc (W q.out), hGC q.out]
    rfl
  have hLHSm : rationalCentreUnipotentQuotientMeasure F =
      HaarQuotient.measure μG (rationalCentreUnipotent F) (rationalCentreUnipotentHaar F) := rfl
  have hRHS : rs22WhittakerIntegral F W W' μ (moduleChar F) (moduleChar_pos F) Φ s =
      ∫ g, Psi F μ Φ s W W' g ∂((μG).withDensity ρN) := by
    rw [rs22WhittakerIntegral_def]
    exact hR.1
  rw [hint, hLHSm]
  refine ⟨hL.2.mpr hΘi, ?_⟩
  rw [hL.1, hStep1, hStep2, integral_congr_ae (Filter.Eventually.of_forall hStep3), hStep4,
    integral_congr_ae (Filter.Eventually.of_forall hStep5), hStep6, hStep7, hRHS]

end Final

end Ws1.V2Asm

end

open Ws1.V2Asm in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (μ ν ω ω' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hωμν : ω * ω' * μ * ν = 1)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦm : Measurable Φ)
      (s : ℂ)
      (W W' : AdelicGL2 (𝓞 F) F → ℂ) (_hWm : Measurable W) (_hW'm : Measurable W')
      (_hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        W (centralScalar (𝓞 F) F z * g) * W' (centralScalar (𝓞 F) F z * g) =
          ((ω z : ℂˣ) : ℂ) * ((ω' z : ℂˣ) : ℂ) * (W g * W' g))
      (_hN : ∀ (n : adelicUnipotent F) (g : AdelicGL2 (𝓞 F) F),
        W ((n : AdelicGL2 (𝓞 F) F) * g) * W' ((n : AdelicGL2 (𝓞 F) F) * g) = W g * W' g)
      (_hunf : Integrable (fun q : UnipotentQuotient F =>
          ‖W q.out * W' q.out * rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s q.out‖)
        (unipotentQuotientMeasure F)),
      Integrable (fun q : RationalCentreUnipotentQuotient F =>
          ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}.indicator
              (fun _ => (1 : ℂ)) q.out) *
            (W q.out * W' q.out) *
            godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s q.out)
        (rationalCentreUnipotentQuotientMeasure F) ∧
      ∫ q : RationalCentreUnipotentQuotient F,
          ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}.indicator
              (fun _ => (1 : ℂ)) q.out) *
            (W q.out * W' q.out) *
            godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s q.out
          ∂(rationalCentreUnipotentQuotientMeasure F) =
        (C : ℂ) * rs22WhittakerIntegral F W W' μ (moduleChar F) (moduleChar_pos F) Φ s :=
  Ws1.V2Asm.main F ν₀ e₁ e₂ he₁ he

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral (solution)
