-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/993e1d3f-6eaa-50de-b3de-6f031e60eb4a

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_NumberField_Idele_exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal NumberField.TateGlobal NumberField.AdelicLevel"

open scoped NNReal ENNReal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.selfDualHaarAt TateLocal.modulus TateLocal.modulus_mul TateLocal.mulMeasure TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "archZeta30 lowerUnipotent21 dualWhittakerFn3 CubicInductionForm CubicInductionForm.factorizable AdelicGL embedMat2 iotaGL coe_iotaGL localMaximalCompact3 componentAtN archComponentN componentAt3 archComponent3 LocalGL3 IsBadPlace diagUnitGL2 diagHom_apply localZeta31 localZeta30 CubicInductionData IsCubicInductionDataOn"
namespace SPartArch
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section LocalUnits

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

variable (w : HeightOneSpectrum (𝓞 ℚ))

theorem borelSpace_loc : BorelSpace (w.adicCompletion ℚ) := borelSpace_localBorel ℚ w

attribute [local instance] borelSpace_loc

theorem borelSpace_locUnits : BorelSpace (w.adicCompletion ℚ)ˣ := by
  refine ⟨?_⟩
  have h : (inferInstance : TopologicalSpace (w.adicCompletion ℚ)ˣ) =
      TopologicalSpace.induced (Units.val : (w.adicCompletion ℚ)ˣ → w.adicCompletion ℚ) inferInstance :=
    Units.isEmbedding_val₀.eq_induced
  show MeasurableSpace.comap Units.val (borel (w.adicCompletion ℚ)) = borel (w.adicCompletion ℚ)ˣ
  exact ((congrArg (fun t => @borel (w.adicCompletion ℚ)ˣ t) h).trans borel_comap).symm

attribute [local instance] borelSpace_locUnits

def locMul : Measure (w.adicCompletion ℚ)ˣ :=
  Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ w))

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ w).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm w.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
    exact_mod_cast (show Ideal.absNorm w.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm w.asIdeal : ℝ≥0) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ w) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm w.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ w) : ℝ) / 2))
    • Measure.addHaarMeasure (integersPositiveCompacts ℚ w) : Measure (w.adicCompletion ℚ))).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

attribute [local instance] isAddHaarMeasure_selfDualHaarAt

theorem range_val :
    Set.range (Units.val : (w.adicCompletion ℚ)ˣ → w.adicCompletion ℚ) = ({0}ᶜ : Set (w.adicCompletion ℚ)) := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩

theorem measurableEmbedding_val :
    MeasurableEmbedding (Units.val : (w.adicCompletion ℚ)ˣ → w.adicCompletion ℚ) :=
  MeasurableEmbedding.iff_comap_eq.mpr ⟨Units.val_injective, rfl, by
    rw [range_val]
    exact (measurableSet_singleton 0).compl⟩

theorem locMul_apply (A : Set (w.adicCompletion ℚ)ˣ) :
    locMul w A = mulMeasure (selfDualHaarAt ℚ w) (Units.val '' A) :=
  (measurableEmbedding_val w).comap_apply _ _

def dens (x : w.adicCompletion ℚ) : ℝ≥0∞ := ((TateLocal.modulus x : ℝ≥0) : ℝ≥0∞)⁻¹

theorem measurable_dens : Measurable (dens w) := by
  have h : dens w = fun x => ((‖x‖₊ : ℝ≥0) : ℝ≥0∞)⁻¹ :=
    funext fun x => by rw [dens, modulus_adicCompletion_eq_nnnorm]
  rw [h]
  exact measurable_nnnorm.coe_nnreal_ennreal.inv

theorem dens_ne_zero (x : w.adicCompletion ℚ) : dens w x ≠ 0 :=
  ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top

theorem mulMeasure_apply_eq (μ : Measure (w.adicCompletion ℚ)) {A : Set (w.adicCompletion ℚ)} (hA : MeasurableSet A) :
    mulMeasure μ A = ∫⁻ x in A ∩ {0}ᶜ, dens w x ∂μ := by
  rw [mulMeasure, withDensity_apply _ hA, Measure.restrict_restrict hA]
  rfl

open scoped Pointwise in

theorem map_mul_left_selfDualHaarAt (u : (w.adicCompletion ℚ)ˣ) :
    Measure.map (fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) (selfDualHaarAt ℚ w) =
      ((distribHaarChar (w.adicCompletion ℚ) u : ℝ≥0∞))⁻¹ • selfDualHaarAt ℚ w := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hset : (fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [Set.mem_inv_smul_set_iff, Set.mem_preimage, Units.smul_def, smul_eq_mul]
  rw [hset, ← distribHaarChar_mul (selfDualHaarAt ℚ w) u⁻¹ s, map_inv,
    ENNReal.coe_inv ((distribHaarChar_pos (A := w.adicCompletion ℚ) (g := u)).ne')]

theorem mulMeasure_preimage_mul_left (u : (w.adicCompletion ℚ)ˣ) {B : Set (w.adicCompletion ℚ)}
    (hB : MeasurableSet B) :
    mulMeasure (selfDualHaarAt ℚ w) ((fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) ⁻¹' B) =
      mulMeasure (selfDualHaarAt ℚ w) B := by
  set T : w.adicCompletion ℚ → w.adicCompletion ℚ := fun x => (u : w.adicCompletion ℚ) * x with hT
  have hmeas : Measurable T := measurable_const_mul _
  set χ : ℝ≥0∞ := (distribHaarChar (w.adicCompletion ℚ) u : ℝ≥0∞) with hχ
  have hχ0 : χ ≠ 0 := ENNReal.coe_ne_zero.mpr (distribHaarChar_pos (A := w.adicCompletion ℚ) (g := u)).ne'
  have hχtop : χ ≠ ⊤ := ENNReal.coe_ne_top
  have hdens : ∀ x : w.adicCompletion ℚ, dens w x = χ * dens w (T x) := by
    intro x
    simp only [dens, hT, TateLocal.modulus_mul, modulus_coe_units, ENNReal.coe_mul, hχ]
    rw [ENNReal.mul_inv (Or.inl hχ0) (Or.inl hχtop), ← mul_assoc, ENNReal.mul_inv_cancel hχ0 hχtop, one_mul]
  have hB' : MeasurableSet (B ∩ {0}ᶜ) := hB.inter (measurableSet_singleton 0).compl
  rw [mulMeasure_apply_eq w _ (hmeas hB), mulMeasure_apply_eq w _ hB]
  have hpre : T ⁻¹' B ∩ {0}ᶜ = T ⁻¹' (B ∩ {0}ᶜ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, hT,
      Units.mul_right_eq_zero]
  rw [hpre]
  calc ∫⁻ x in T ⁻¹' (B ∩ {0}ᶜ), dens w x ∂(selfDualHaarAt ℚ w)
      = ∫⁻ x in T ⁻¹' (B ∩ {0}ᶜ), χ * dens w (T x) ∂(selfDualHaarAt ℚ w) :=
        setLIntegral_congr_fun (hmeas hB') fun x _ => hdens x
    _ = χ * ∫⁻ x in T ⁻¹' (B ∩ {0}ᶜ), dens w (T x) ∂(selfDualHaarAt ℚ w) :=
        lintegral_const_mul χ ((measurable_dens w).comp hmeas)
    _ = χ * ∫⁻ y in B ∩ {0}ᶜ, dens w y ∂(Measure.map T (selfDualHaarAt ℚ w)) := by
        rw [setLIntegral_map hB' (measurable_dens w) hmeas]
    _ = χ * (χ⁻¹ * ∫⁻ y in B ∩ {0}ᶜ, dens w y ∂(selfDualHaarAt ℚ w)) := by
        rw [map_mul_left_selfDualHaarAt, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = ∫⁻ y in B ∩ {0}ᶜ, dens w y ∂(selfDualHaarAt ℚ w) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hχ0 hχtop, one_mul]

theorem image_val_preimage_mul_left (u : (w.adicCompletion ℚ)ˣ) (A : Set (w.adicCompletion ℚ)ˣ) :
    Units.val '' ((fun y => u * y) ⁻¹' A) =
      (fun x : w.adicCompletion ℚ => (u : w.adicCompletion ℚ) * x) ⁻¹' (Units.val '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨u * y, hy, by rw [Units.val_mul]⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨u⁻¹ * z, by simpa using hz, ?_⟩
    have hzx' : (z : w.adicCompletion ℚ) = (u : w.adicCompletion ℚ) * x := hzx
    rw [Units.val_mul, hzx', ← mul_assoc, Units.inv_mul, one_mul]

theorem isMulLeftInvariant_locMul : (locMul w).IsMulLeftInvariant := by
  refine ⟨fun u => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul u) hA, locMul_apply, locMul_apply, image_val_preimage_mul_left]
  exact mulMeasure_preimage_mul_left w u ((measurableEmbedding_val w).measurableSet_image.mpr hA)

theorem isFiniteMeasureOnCompacts_locMul : IsFiniteMeasureOnCompacts (locMul w) := by
  refine ⟨fun C hC => ?_⟩
  have hCK : IsCompact (Units.val '' C) := hC.image Units.continuous_val
  rw [locMul_apply, mulMeasure_apply_eq w _ hCK.measurableSet]
  obtain ⟨M, hM⟩ := (hC.image ((continuous_nnnorm.comp Units.continuous_coe_inv))).bddAbove
  have hle : ∀ x ∈ Units.val '' C ∩ {0}ᶜ, dens w x ≤ (M : ℝ≥0∞) := by
    rintro _ ⟨⟨u, hu, rfl⟩, -⟩
    have h1 : dens w (u : w.adicCompletion ℚ) = ((‖((u⁻¹ : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ)‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [dens, modulus_adicCompletion_eq_nnnorm, Units.val_inv_eq_inv_val, nnnorm_inv,
        ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr u.ne_zero)]
    rw [h1]
    exact ENNReal.coe_le_coe.mpr (hM ⟨u, hu, rfl⟩)
  calc ∫⁻ x in Units.val '' C ∩ {0}ᶜ, dens w x ∂(selfDualHaarAt ℚ w)
      ≤ ∫⁻ x in Units.val '' C ∩ {0}ᶜ, (M : ℝ≥0∞) ∂(selfDualHaarAt ℚ w) := setLIntegral_mono measurable_const hle
    _ = (M : ℝ≥0∞) * selfDualHaarAt ℚ w (Units.val '' C ∩ {0}ᶜ) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top
        ((measure_mono Set.inter_subset_left).trans_lt hCK.measure_lt_top)

theorem isOpenPosMeasure_locMul : (locMul w).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  have hUo : IsOpen (Units.val '' U) := (IsOpenUnits.isOpenEmbedding_unitsVal).isOpenMap _ hU
  have hsub : Units.val '' U ∩ {0}ᶜ = Units.val '' U :=
    Set.inter_eq_self_of_subset_left (by rw [← range_val]; exact Set.image_subset_range _ _)
  rw [locMul_apply, mulMeasure_apply_eq w _ hUo.measurableSet, hsub]
  intro h0
  have hae := (lintegral_eq_zero_iff (measurable_dens w)).mp h0
  rw [Filter.EventuallyEq, ae_iff] at hae
  have huniv : {x : w.adicCompletion ℚ | ¬dens w x = (0 : (w.adicCompletion ℚ) → ℝ≥0∞) x} = Set.univ :=
    Set.eq_univ_of_forall fun x => dens_ne_zero w x
  rw [huniv, Measure.restrict_apply_univ] at hae
  exact hUo.measure_ne_zero (selfDualHaarAt ℚ w) (hne.image _) hae

theorem isHaarMeasure_locMul : (locMul w).IsHaarMeasure :=
  @Measure.IsHaarMeasure.mk _ _ _ _ _ (isFiniteMeasureOnCompacts_locMul w) (isMulLeftInvariant_locMul w)
    (isOpenPosMeasure_locMul w)

end LocalUnits

section Components

theorem componentAt3_iotaGL_diagUnitGL2 (w : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    componentAt3 (𝓞 ℚ) ℚ w (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (M4aHerbrand.finPart w a)) := by
  refine Units.ext ?_
  ext i j
  rw [componentAt3, componentAtN, Matrix.GeneralLinearGroup.map_apply, coe_iotaGL, coe_iotaGL]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]
  rfl

theorem archComponent3_iotaGL_diagUnitGL2 (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (M4aHerbrand.infPart a)) := by
  refine Units.ext ?_
  ext i j
  rw [archComponent3, archComponentN, Matrix.GeneralLinearGroup.map_apply, coe_iotaGL, coe_iotaGL]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]
  rfl

theorem diagUnitGL2_one {A : Type*} [CommRing A] : diagUnitGL2 (1 : Aˣ) = 1 := by
  rw [← diagHom_apply]
  exact map_one _

end Components

section Idele

variable {F : Type} [Field F] [NumberField F]

def archEmbed : (InfiniteAdeleRing F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def locEmbed (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F w)

theorem coe_archEmbed (u : (InfiniteAdeleRing F)ˣ) :
    ((archEmbed u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = ((u : InfiniteAdeleRing F), 1) := rfl

theorem infPart_archEmbed (u : (InfiniteAdeleRing F)ˣ) : M4aHerbrand.infPart (archEmbed (F := F) u) = u :=
  Units.ext rfl

theorem finPart_archEmbed (w : HeightOneSpectrum (𝓞 F)) (u : (InfiniteAdeleRing F)ˣ) :
    M4aHerbrand.finPart w (archEmbed (F := F) u) = 1 :=
  Units.ext rfl

theorem infPart_locEmbed (w : HeightOneSpectrum (𝓞 F)) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.infPart (locEmbed (F := F) w t) = 1 :=
  Units.ext rfl

theorem finPart_locEmbed_self (w : HeightOneSpectrum (𝓞 F)) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.finPart w (locEmbed (F := F) w t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F w t)

theorem finPart_locEmbed_of_ne {w w' : HeightOneSpectrum (𝓞 F)} (h : w' ≠ w) (t : (w.adicCompletion F)ˣ) :
    M4aHerbrand.finPart w' (locEmbed (F := F) w t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F w t h)

theorem idele_ext {a b : (AdeleRing (𝓞 F) F)ˣ} (h₁ : M4aHerbrand.infPart a = M4aHerbrand.infPart b)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F), M4aHerbrand.finPart w a = M4aHerbrand.finPart w b) : a = b := by
  refine Units.ext (Prod.ext ?_ ?_)
  · exact congrArg Units.val h₁
  · refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    exact congrArg Units.val (h₂ v)

theorem eq_archEmbed_mul_prod (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) :
    a = archEmbed (M4aHerbrand.infPart a) * ∏ w ∈ S, locEmbed w (M4aHerbrand.finPart w a) := by
  refine idele_ext ?_ fun w' => ?_
  · rw [map_mul, map_prod, infPart_archEmbed, Finset.prod_eq_one fun w _ => infPart_locEmbed w _, mul_one]
  · rw [map_mul, map_prod, finPart_archEmbed, one_mul]
    by_cases hw' : w' ∈ S
    · rw [Finset.prod_eq_single w' (fun w _ hne => finPart_locEmbed_of_ne (Ne.symm hne) _)
        (fun h => absurd hw' h), finPart_locEmbed_self]
    · rw [Finset.prod_eq_one fun w hw => finPart_locEmbed_of_ne (by rintro rfl; exact hw' hw) _]
      exact Units.ext (ha w' hw')

theorem char_eq_arch_mul_prod_localChar (τ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (AdeleRing (𝓞 F) F)ˣ) (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) :
    ((τ a : ℂˣ) : ℂ) =
      ((τ (archEmbed (M4aHerbrand.infPart a)) : ℂˣ) : ℂ) *
        ∏ w ∈ S, ((localChar τ w (M4aHerbrand.finPart w a) : ℂˣ) : ℂ) := by
  conv_lhs => rw [eq_archEmbed_mul_prod S a ha]
  rw [map_mul, Units.val_mul, map_prod, Units.coe_prod]
  rfl

theorem ideleNorm_eq_norm_mul_prod_modulus (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) :
    ideleNorm F a = ‖(a : AdeleRing (𝓞 F) F).1‖ * ∏ w ∈ S, ((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ) := by
  rw [ideleNorm, NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F a,
    ← InfiniteAdeleRing.norm_def]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
  · exact Finset.prod_congr rfl fun w _ => by rw [modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
  · intro w hw
    by_contra hwS
    exact hw (show ‖(a : AdeleRing (𝓞 F) F).2 w‖ = 1 by rw [ha w hwS, norm_one])

theorem cpow_prod_ofReal_nonneg {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (z : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z := by
  classical
  refine @Finset.induction_on ι (fun s => (∀ i ∈ s, 0 ≤ r i) →
      (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z) _ s (fun _ => by simp) ?_ hr
  intro a s ha ih hr
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (hr a (Finset.mem_insert_self a s))
      (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)) z,
    ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

theorem ideleNorm_cpow_eq (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) (z : ℂ) :
    ((ideleNorm F a : ℝ) : ℂ) ^ z =
      ((‖(a : AdeleRing (𝓞 F) F).1‖ : ℝ) : ℂ) ^ z *
        ∏ w ∈ S, ((((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ) : ℂ)) ^ z := by
  have h1 : (0 : ℝ) ≤ ‖(a : AdeleRing (𝓞 F) F).1‖ := by
    rw [InfiniteAdeleRing.norm_def]
    exact Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _
  have h2 : (0 : ℝ) ≤ ∏ w ∈ S, ((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ) :=
    Finset.prod_nonneg fun w _ => NNReal.coe_nonneg _
  rw [ideleNorm_eq_norm_mul_prod_modulus S a ha, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h1 h2 z,
    cpow_prod_ofReal_nonneg S (fun w => ((modulus ((a : AdeleRing (𝓞 F) F).2 w) : ℝ≥0) : ℝ))
      (fun w _ => NNReal.coe_nonneg _)]

end Idele

section Arch

theorem archEmbed_eq_of (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (u : (InfiniteAdeleRing ℚ)ˣ) : archEmbed u = E u := by
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := congrArg Units.val (hE u).1
    rw [M4aHerbrand.coe_infPart_apply] at h
    exact h.symm
  · have h := congrArg Units.val (hE u).2
    rw [Units.val_one] at h
    exact h.symm

end Arch

section Integrands

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

def gDir (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (χ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) (u : (InfiniteAdeleRing ℚ)ˣ) : ℂ :=
  Warch (iotaGL (diagUnitGL2 u) * 1 * garch) * ((χ u : ℂˣ) : ℂ) *
    ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)

theorem integral_gDir {mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ} (ν : Measure (InfiniteAdeleRing ℚ)ˣ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (χ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) :
    ∫ u, gDir Warch χ garch s u ∂ν = archZeta30 ν (fun h => Warch (h * garch)) χ s 1 :=
  rfl

def hDir (w : HeightOneSpectrum (𝓞 ℚ)) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) (t : (w.adicCompletion ℚ)ˣ) : ℂ :=
  Wloc (iotaGL (diagUnitGL2 t) * gw) * ((χ t : ℂˣ) : ℂ) *
    ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)

theorem integral_hDir (w : HeightOneSpectrum (𝓞 ℚ)) {mT : MeasurableSpace (w.adicCompletion ℚ)ˣ}
    (μ : Measure (w.adicCompletion ℚ)ˣ) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) :
    ∫ t, hDir w Wloc χ gw s t ∂μ = localZeta30 w μ Wloc χ s gw :=
  rfl

open scoped Classical in

def gDual (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (χ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) (u : (InfiniteAdeleRing ℚ)ˣ) : ℂ :=
  (∫ y : mixedEmbedding.mixedSpace ℚ,
      dualWhittakerFn3 Warch (iotaGL (diagUnitGL2 u) * 1 *
        lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * garch)) * ((χ u : ℂˣ) : ℂ) *
    ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)

open scoped Classical in

theorem integral_gDual {mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ} (ν : Measure (InfiniteAdeleRing ℚ)ˣ)
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (χ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (garch : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ) :
    ∫ u, gDual Warch χ garch s u ∂ν =
      archZeta30 ν (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
        dualWhittakerFn3 Warch (h * lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * garch))
        χ s 1 :=
  rfl

def cO (w : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  (((selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) : ℂ))⁻¹

def hDual (w : HeightOneSpectrum (𝓞 ℚ)) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) (t : (w.adicCompletion ℚ)ˣ) : ℂ :=
  cO w * ((∫ x : w.adicCompletion ℚ,
      dualWhittakerFn3 Wloc (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * gw) ∂(selfDualHaarAt ℚ w)) *
    ((χ t : ℂˣ) : ℂ) * ((TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))

theorem integral_hDual (w : HeightOneSpectrum (𝓞 ℚ)) {mT : MeasurableSpace (w.adicCompletion ℚ)ˣ}
    (μ : Measure (w.adicCompletion ℚ)ˣ) (Wloc : LocalGL3 w → ℂ) (χ : (w.adicCompletion ℚ)ˣ →* ℂˣ)
    (gw : LocalGL3 w) (s : ℂ) :
    ∫ t, hDual w Wloc χ gw s t ∂μ =
      cO w * localZeta31 w μ (selfDualHaarAt ℚ w) (dualWhittakerFn3 Wloc) χ s gw :=
  integral_const_mul _ _

end Integrands

section Pointwise

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

variable {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
  {pins : AutomorphicForm.CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}

theorem whittaker_iotaGL_diagUnitGL2_mul (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (ha : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → (a : AdeleRing (𝓞 ℚ) ℚ).2 w = 1) :
    X.whittaker (iotaGL (diagUnitGL2 a) * g) =
      X.whittakerArch (iotaGL (diagUnitGL2 (M4aHerbrand.infPart a)) * archComponent3 (𝓞 ℚ) ℚ g) *
        ∏ w ∈ S, X.whittakerLoc w (iotaGL (diagUnitGL2 (M4aHerbrand.finPart w a)) * componentAt3 (𝓞 ℚ) ℚ w g) := by
  have h := hX.factorizable (iotaGL (diagUnitGL2 a) * g) S (fun w hw => (hSbad w).mp hw) (fun w hw => by
    rw [map_mul, componentAt3_iotaGL_diagUnitGL2, show M4aHerbrand.finPart w a = 1 from Units.ext (ha w hw),
      diagUnitGL2_one, map_one, one_mul]
    exact hg w hw)
  rw [h, map_mul, archComponent3_iotaGL_diagUnitGL2]
  congr 1
  exact Finset.prod_congr rfl fun w _ => by rw [map_mul, componentAt3_iotaGL_diagUnitGL2]

theorem dir_factor (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w)
    (s : ℂ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → (a : AdeleRing (𝓞 ℚ) ℚ).2 w = 1) :
    X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) =
      gDir X.whittakerArch (τ.comp E) (archComponent3 (𝓞 ℚ) ℚ g) s (M4aHerbrand.infPart a) *
        ∏ w ∈ S, hDir w (X.whittakerLoc w) (localChar τ w) (componentAt3 (𝓞 ℚ) ℚ w g) s (M4aHerbrand.finPart w a) := by
  simp only [gDir, hDir, mul_one, MonoidHom.comp_apply, M4aHerbrand.coe_infPart_apply,
    M4aHerbrand.coe_finPart_apply]
  rw [whittaker_iotaGL_diagUnitGL2_mul X hX S hSbad g hg a ha,
    char_eq_arch_mul_prod_localChar τ S a ha, archEmbed_eq_of E hE, ideleNorm_cpow_eq S a ha (s - 1),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

open scoped Classical in

theorem dual_factor (X : CubicInductionData) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ha : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → (a : AdeleRing (𝓞 ℚ) ℚ).2 w = 1) :
    (∫ y : mixedEmbedding.mixedSpace ℚ,
        dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
          lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
      (∏ v ∈ S,
        (((selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) : ℂ)⁻¹ *
          ∫ x : v.adicCompletion ℚ,
            dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
              lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g) ∂(selfDualHaarAt ℚ v))) *
      ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) =
      gDual X.whittakerArch (τ.comp E) (archComponent3 (𝓞 ℚ) ℚ g) s (M4aHerbrand.infPart a) *
        ∏ w ∈ S, hDual w (X.whittakerLoc w) (localChar τ w) (componentAt3 (𝓞 ℚ) ℚ w g) s
          (M4aHerbrand.finPart w a) := by
  simp only [gDual, hDual, cO, mul_one, MonoidHom.comp_apply, M4aHerbrand.coe_infPart_apply,
    M4aHerbrand.coe_finPart_apply, archComponent3_iotaGL_diagUnitGL2, componentAt3_iotaGL_diagUnitGL2]
  rw [char_eq_arch_mul_prod_localChar τ S a ha, archEmbed_eq_of E hE, ideleNorm_cpow_eq S a ha (s - 1)]
  simp only [Finset.prod_mul_distrib]
  ring

end Pointwise

end LanglandsTunnell.CubicInduction.SPartArch

end

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg"

open scoped Classical in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSbad : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (hS : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (hS' : ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ σ₀ : ℝ,
      ∀ s : ℂ, σ₀ < s.re →
        Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
          (NumberField.Idele.productMeasureData ℚ S).νS)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∈ S)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ cS : ℂ, cS ≠ 0 ∧
      (∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
          componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
              X.whittaker (iotaGL (diagUnitGL2 a) * g) * ((τ a : ℂˣ) : ℂ) *
                ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.productMeasureData ℚ S).νS) =
            cS *
              archZeta30 ν_mul (fun h => X.whittakerArch (h * archComponent3 (𝓞 ℚ) ℚ g)) (τ.comp E) s 1 *
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               localZeta30 v (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                (X.whittakerLoc v) (localChar τ v) s (componentAt3 (𝓞 ℚ) ℚ v g)) *
              ∏ w ∈ S.erase v,
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                 localZeta30 w (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                  (X.whittakerLoc w) (localChar τ w) s (componentAt3 (𝓞 ℚ) ℚ w g))) ∧
      ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S →
          componentAt3 (𝓞 ℚ) ℚ w g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ w) →
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.productMeasureData ℚ S).νS) =
            cS *
              archZeta30 ν_mul (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
                dualWhittakerFn3 X.whittakerArch (h *
                  lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g))
                (τ.comp E) s 1 *
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 localZeta31 v (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)))
                  (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) (dualWhittakerFn3 (X.whittakerLoc v))
                  (localChar τ v) s (componentAt3 (𝓞 ℚ) ℚ v g)) *
              ∏ w ∈ S.erase v,
                (letI := LanglandsTunnell.TateLocal.localBorel ℚ w
                 ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w).real (w.adicCompletionIntegers ℚ : Set
                   (w.adicCompletion ℚ)) : ℂ)⁻¹ *
                   localZeta31 w (Measure.comap Units.val
                  (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)))
                    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w) (dualWhittakerFn3 (X.whittakerLoc w))
                    (localChar τ w) s (componentAt3 (𝓞 ℚ) ℚ w g)) := by
  have hB : ∀ w : HeightOneSpectrum (𝓞 ℚ), @BorelSpace (w.adicCompletion ℚ)ˣ _
      (@Units.instMeasurableSpace _ _ (LanglandsTunnell.TateLocal.localBorel ℚ w)) :=
    fun w => LanglandsTunnell.CubicInduction.SPartArch.borelSpace_locUnits w
  obtain ⟨c, hc, hfac⟩ :=
    @NumberField.Idele.exists_integral_sPartMeasure_eq_mul_integral_mul_prod_integral ℚ _ _ S mT _ ν_mul _
      (fun w => @Units.instMeasurableSpace _ _ (LanglandsTunnell.TateLocal.localBorel ℚ w)) hB
      (fun w => LanglandsTunnell.CubicInduction.SPartArch.locMul w)
      (fun w _ => LanglandsTunnell.CubicInduction.SPartArch.isHaarMeasure_locMul w)
  refine ⟨(c : ℂ), Complex.ofReal_ne_zero.mpr hc.ne', ?_, ?_⟩
  · intro τ hτ g hg
    obtain ⟨σ₀, hσ⟩ := hS τ hτ g
    refine ⟨σ₀, fun s hs => ?_⟩
    have key := hfac _ _ _
      (fun a ha => LanglandsTunnell.CubicInduction.SPartArch.dir_factor X hX S hSbad τ E hE g hg s a ha)
      (hσ s hs).aestronglyMeasurable
    refine key.trans ?_
    rw [LanglandsTunnell.CubicInduction.SPartArch.integral_gDir]
    simp only [LanglandsTunnell.CubicInduction.SPartArch.integral_hDir]
    rw [← Finset.mul_prod_erase S (fun w => localZeta30 w (LanglandsTunnell.CubicInduction.SPartArch.locMul w)
      (X.whittakerLoc w) (localChar τ w) s (componentAt3 (𝓞 ℚ) ℚ w g)) hv]
    simp only [LanglandsTunnell.CubicInduction.SPartArch.locMul]
    ring
  · intro τ hτ g hg
    obtain ⟨σ₀, hσ⟩ := hS' τ hτ g
    refine ⟨σ₀, fun s hs => ?_⟩
    have key := hfac _ _ _
      (fun a ha => LanglandsTunnell.CubicInduction.SPartArch.dual_factor X S τ E hE g s a ha)
      (hσ s hs).aestronglyMeasurable
    refine key.trans ?_
    rw [LanglandsTunnell.CubicInduction.SPartArch.integral_gDual]
    simp only [LanglandsTunnell.CubicInduction.SPartArch.integral_hDual]
    rw [← Finset.mul_prod_erase S (fun w => LanglandsTunnell.CubicInduction.SPartArch.cO w *
      localZeta31 w (LanglandsTunnell.CubicInduction.SPartArch.locMul w) (selfDualHaarAt ℚ w)
        (dualWhittakerFn3 (X.whittakerLoc w)) (localChar τ w) s (componentAt3 (𝓞 ℚ) ℚ w g)) hv]
    simp only [LanglandsTunnell.CubicInduction.SPartArch.locMul, LanglandsTunnell.CubicInduction.SPartArch.cO]
    ring

end S_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_sPart_eq_arch_mul_localZeta_v_mul_badPlacesPart_archTwisted_of_isCubicInductionDataOn (solution)
