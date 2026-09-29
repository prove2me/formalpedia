-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cde3b72f-1eb0-5972-9e04-9429af1131c3

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Theorems.Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
import Theorems.Thm_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_ne_zero_of_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_adelicGL3_archComponent3_eq_one_componentAt3_eq
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_twist_det_localPackage
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
import Theorems.Thm_LanglandsTunnell_finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.CubicInduction.fnTwist3_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors"
set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction~det_upperUnipotent3 MeasureTheory"
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

set_option autoImplicit false

section Ws23IsoKitPlace

open IsDedekindDomain NumberField Matrix AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3"
open NumberField.AdelicLevel NumberField.AdelicVolume

noncomputable section

namespace Ws23Iso

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem glMap_apply {A B : Type*} [CommRing A] [CommRing B] {n : Type*} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) (i j : n) :
    ((Matrix.GeneralLinearGroup.map φ g : GL n B) : Matrix n n B) i j = φ ((g : Matrix n n A) i j) := rfl

theorem map_iotaGL {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.map φ (iotaGL g) = iotaGL (Matrix.GeneralLinearGroup.map φ g) := by
  ext i j
  rw [glMap_apply, coe_iotaGL, coe_iotaGL]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem localAt_eq (p : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    localAt ℚ p g = finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) := rfl

theorem componentAt3_iota (v : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ g) = iotaGL (localAt ℚ v g) := by
  have h : localAt ℚ v g =
      Matrix.GeneralLinearGroup.map ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)) g := by
    ext i j
    rfl
  rw [h]
  exact map_iotaGL _ g

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem glArch_archRealGLAt_ratArchGL2 (g : G2) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) =
      glArch (𝓞 ℚ) ℚ g := by
  have h := (RSCarrier.finFactor g).2
  rw [mem_finiteAdelicGL2Subgroup_iff, coe_finFactor, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glFin_finFactor (g : G2) : glFin (𝓞 ℚ) ℚ (RSCarrier.finFactor g : G2) = glFin (𝓞 ℚ) ℚ g := by
  rw [coe_finFactor, map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul]

theorem localAt_finFactor (p : HeightOneSpectrum (𝓞 ℚ)) (g : G2) :
    localAt ℚ p (RSCarrier.finFactor g : G2) = localAt ℚ p g := by
  rw [localAt_eq, localAt_eq, glFin_finFactor]

theorem localAt_archRealGLAt (p : HeightOneSpectrum (𝓞 ℚ)) (m : GL (Fin 2) ℝ) :
    localAt ℚ p (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 := by
  rw [localAt_eq, glFin_archRealGLAt, map_one]

theorem ratArchGL2_mul (g h : G2) : ratArchGL2 (g * h) = ratArchGL2 g * ratArchGL2 h := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_mul, map_mul, map_mul]

theorem ratArchGL2_inv (g : G2) : ratArchGL2 g⁻¹ = (ratArchGL2 g)⁻¹ := by
  unfold LanglandsTunnell.ratArchGL2; rw [map_inv, map_inv, map_inv]

theorem ratArchGL2_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev w0 : InfinitePlace ℚ := default
theorem hw0 : (w0).IsReal := IsTotallyReal.isReal _
abbrev eR : (w0).Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal hw0
abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hw0

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = w0 := Subsingleton.elim _ _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 v =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl := infinitePlace_eq v
  show archMatrixUpdate ℚ w0 ((glEquivOfRingEquiv (eR).symm M : GL (Fin 2) (w0).Completion) : Matrix _ _ _) i j w0 = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem ratArchGL2_apply (g : G2) (i j : Fin 2) :
    ((ratArchGL2 g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = eR (((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0) := rfl

theorem ratArchGL2_archRealGLAt (M : GL (Fin 2) ℝ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M) = M := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [ratArchGL2_apply]
  show eR ((((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w0) = _
  rw [iotaR_fst]
  exact (eR).apply_symm_apply _

theorem ratArchGL2_finFactor (g : G2) : ratArchGL2 (RSCarrier.finFactor g : G2) = 1 :=
  ratArchGL2_of_mem (RSCarrier.finFactor g).2

theorem finFactor_coe (gf : finiteAdelicGL2Subgroup ℚ) : RSCarrier.finFactor (gf : G2) = gf := by
  refine Subtype.ext ?_
  rw [coe_finFactor, ratArchGL2_of_mem gf.2, map_one, inv_one, one_mul]

theorem finFactor_finFactor (g : G2) : RSCarrier.finFactor (RSCarrier.finFactor g : G2) = RSCarrier.finFactor g :=
  finFactor_coe _

theorem ratArchGL2_archRealGLAt_mul (M : GL (Fin 2) ℝ) (gf : finiteAdelicGL2Subgroup ℚ) :
    ratArchGL2 (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M * (gf : G2)) = M := by
  rw [ratArchGL2_mul, ratArchGL2_archRealGLAt, ratArchGL2_of_mem gf.2, mul_one]

theorem finFactor_archRealGLAt_mul (M : GL (Fin 2) ℝ) (gf : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M * (gf : G2)) = gf := by
  refine Subtype.ext ?_
  rw [coe_finFactor, ratArchGL2_archRealGLAt_mul, inv_mul_cancel_left]

theorem abs_det_ratArchGL2 (g : G2) :
    |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| = archDetNorm (default : InfinitePlace ℚ) g := by
  unfold archDetNorm LanglandsTunnell.ratArchGL2
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hcoe : ((Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
        (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom.mapMatrix
        ((archComponent ℚ default (glArch (𝓞 ℚ) ℚ g) : GL (Fin 2) (default : InfinitePlace ℚ).Completion) :
          Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) := rfl
  rw [hcoe, ← RingHom.map_det, ← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _) _

theorem detNorm_eq_archAbs_mul_finNorm (g : G2) :
    detNorm g = |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| *
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : G2)) := by
  have hg : archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g) *
      (RSCarrier.finFactor g : G2) = g := by
    rw [coe_finFactor, mul_inv_cancel_left]
  conv_lhs => rw [← hg]
  unfold detNorm
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  congr 1
  have hX : glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) ∈
      finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [glFin_archRealGLAt]; exact one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ _ hX, Fintype.prod_subsingleton _ default]
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [NumberField.InfinitePlace.mult, IsTotallyReal.isReal]
  rw [hmult, pow_one, abs_det_ratArchGL2]
  unfold archDetNorm
  rw [glArch_archRealGLAt_ratArchGL2]

theorem detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow (g : G2) (z : ℂ) :
    ((detNorm g : ℝ) : ℂ) ^ z =
      (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ z) *
        ((TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ z) := by
  rw [detNorm_eq_archAbs_mul_finNorm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (NumberField.TateGlobal.ideleNorm_pos _).le]

theorem detNorm_coe_fin (gf : finiteAdelicGL2Subgroup ℚ) :
    detNorm (gf : G2) = TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : G2)) := rfl

theorem detNorm_pos (g : G2) : 0 < detNorm g := NumberField.TateGlobal.ideleNorm_pos _

theorem continuous_detNorm : Continuous (detNorm : G2 → ℝ) :=
  NumberField.TateGlobal.continuous_ideleNorm_det ℚ

end Ws23Iso

end

end Ws23IsoKitPlace

section Ws23RefA

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction~det_upperUnipotent3 NumberField.AdelicLevel NumberField.AdelicVolume"
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws23Iso

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

scoped instance isAddHaarMeasure_adelicAddHaar_refA : (μA).IsAddHaarMeasure :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

abbrev pinsQ (D : Set G2) : CarrierPins ℚ :=
  productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) (AdelicBox.adelicBox ℚ)

theorem W_apply (D : Set G2) (χ : AddChar 𝔸 ℂ) (f : G2 → ℂ) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ f 1 g = ∫ x, f (unipotentGL2 x * g) * χ (-x)
      ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ)) := by
  show (∫ x, f (unipotentGL2 x * g) * χ (-(algebraMap ℚ 𝔸 1 * x)) ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ))) = _
  congr 1; funext x; rw [map_one, one_mul]

theorem integrable_cond_adelicBox {f : 𝔸 → ℂ} (hf : Continuous f) :
    Integrable f (ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ)) := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset (K := ℚ)
  have h1 : IntegrableOn f (AdelicBox.adelicBox ℚ) μA := (hf.continuousOn.integrableOn_compact hC).mono_set hsub
  have hcond : ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ) =
      ((μA) (AdelicBox.adelicBox ℚ))⁻¹ • (μA).restrict (AdelicBox.adelicBox ℚ) := rfl
  rw [hcond]
  exact h1.integrable.smul_measure (ENNReal.inv_ne_top.2 (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos (K := ℚ)).ne')

theorem W_finsum (D : Set G2) (χ : AddChar 𝔸 ℂ) (hχ : Continuous χ) {n : ℕ} (c : Fin n → ℂ) (f : Fin n → G2 → ℂ)
    (hf : ∀ i, Continuous (f i)) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ (fun z => ∑ i, c i * f i z) 1 g =
      ∑ i, c i * whittakerCoefficient ℚ (pinsQ D) χ (f i) 1 g := by
  rw [W_apply]
  simp_rw [W_apply, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  · have hc : Continuous fun y : 𝔸 => c i * f i (unipotentGL2 y * g) * χ (-y) :=
      (continuous_const.mul ((hf i).comp ((AutomorphicForm.continuous_unipotentGL2 (R := 𝔸)).mul continuous_const))).mul
        (hχ.comp continuous_neg)
    exact integrable_cond_adelicBox hc

theorem W_translate (D : Set G2) (χ : AddChar 𝔸 ℂ) (f : G2 → ℂ) (k g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ (fun z => f (z * k)) 1 g = whittakerCoefficient ℚ (pinsQ D) χ f 1 (g * k) := by
  rw [W_apply, W_apply]
  simp only [mul_assoc]

theorem W_mul_invariant (D : Set G2) (χ : AddChar 𝔸 ℂ) (a f : G2 → ℂ)
    (ha : ∀ (x : 𝔸) (g : G2), a (unipotentGL2 x * g) = a g) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ (fun z => a z * f z) 1 g = a g * whittakerCoefficient ℚ (pinsQ D) χ f 1 g := by
  rw [W_apply, W_apply, ← integral_const_mul]
  congr 1; funext x; rw [ha]; ring

theorem detNorm_unipotentGL2_mul (x : 𝔸) (g : G2) : detNorm (unipotentGL2 x * g) = detNorm g := by
  unfold detNorm
  have : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G2) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Units.val_one, Matrix.det_fin_two_of]
    ring
  rw [map_mul, this, one_mul]

theorem detNorm_mul (g h : G2) : detNorm (g * h) = detNorm g * detNorm h := by
  unfold detNorm; rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]

abbrev fstM (g : G2) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) :=
  (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)
abbrev sndM (g : G2) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) 𝔸)

theorem fstM_mul (g h : G2) : fstM (g * h) = fstM g * fstM h := (RingHom.mapMatrix _).map_mul _ _
theorem sndM_mul (g h : G2) : sndM (g * h) = sndM g * sndM h := (RingHom.mapMatrix _).map_mul _ _

theorem eq_of_fstM_sndM {g h : G2} (h1 : fstM g = fstM h) (h2 : sndM g = sndM h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem fstM_eq_one_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : fstM g = 1 := by
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg
  exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) hg

theorem iotaR_snd (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j := rfl

theorem sndM_iotaR (M : GL (Fin 2) ℝ) : sndM (ιR M) = 1 := Matrix.ext fun i j => iotaR_snd M i j

theorem iotaR_mul_comm {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) (M : GL (Fin 2) ℝ) : ιR M * g = g * ιR M := by
  refine eq_of_fstM_sndM ?_ ?_
  · rw [fstM_mul, fstM_mul, fstM_eq_one_of_mem hg, mul_one, one_mul]
  · rw [sndM_mul, sndM_mul, sndM_iotaR, mul_one, one_mul]

theorem finFactor_mul_archRealGLAt (g : G2) (M : GL (Fin 2) ℝ) :
    RSCarrier.finFactor (g * ιR M) = RSCarrier.finFactor g := by
  refine Subtype.ext ?_
  have hc := iotaR_mul_comm (RSCarrier.finFactor g).2 M
  rw [coe_finFactor] at hc
  rw [coe_finFactor, coe_finFactor, ratArchGL2_mul, ratArchGL2_archRealGLAt, map_mul, mul_inv_rev]
  calc (ιR M)⁻¹ * (ιR (ratArchGL2 g))⁻¹ * (g * ιR M)
      = (ιR M)⁻¹ * (((ιR (ratArchGL2 g))⁻¹ * g) * ιR M) := by simp only [mul_assoc]
    _ = (ιR M)⁻¹ * (ιR M * ((ιR (ratArchGL2 g))⁻¹ * g)) := by rw [hc]
    _ = (ιR (ratArchGL2 g))⁻¹ * g := by rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem finFactor_mul_of_mem (g : G2) {x : G2} (hx : x ∈ finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (g * x) = RSCarrier.finFactor ((RSCarrier.finFactor g : G2) * x) := by
  refine Subtype.ext ?_
  rw [coe_finFactor, coe_finFactor, ratArchGL2_mul, ratArchGL2_of_mem hx, mul_one, ratArchGL2_mul,
    ratArchGL2_finFactor, ratArchGL2_of_mem hx, mul_one, map_one, inv_one, one_mul, coe_finFactor, mul_assoc]

theorem placeEmbed_mem_fin (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    UnramifiedWhittaker.placeEmbed ℚ p x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

end Ws23Iso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end Ws23RefA
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23RefA2

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction~det_upperUnipotent3 NumberField.AdelicLevel NumberField.AdelicVolume"
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws23Iso

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

theorem coe_finFactor_of_mem {y : G2} (hy : y ∈ finiteAdelicGL2Subgroup ℚ) : (RSCarrier.finFactor y : G2) = y := by
  rw [coe_finFactor, ratArchGL2_of_mem hy, map_one, inv_one, one_mul]

theorem ratArchGL2_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    ratArchGL2 (UnramifiedWhittaker.placeEmbed ℚ p x) = 1 :=
  ratArchGL2_of_mem (placeEmbed_mem_fin p x)

theorem whittakerCoefficient_purified_archTranslate (D : Set G2) (χ : AddChar 𝔸 ℂ) (hχ : Continuous χ)
    (φ : G2 → ℂ) (hφ : Continuous φ) (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ g : G2, whittakerCoefficient ℚ (pinsQ D) χ φ 1 g = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g))
    (p : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (c : Fin n → ℂ) (x : Fin n → GL (Fin 2) (p.adicCompletion ℚ))
    (hA : GL (Fin 2) ℝ) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ
        (fun g : G2 => ∑ j, c j * (((detNorm (g * UnramifiedWhittaker.placeEmbed ℚ p (x j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
          φ (g * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA))) 1 g =
      ((((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA (ratArchGL2 g * hA)) *
        ∑ j, c j * (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
            ((RSCarrier.finFactor g : G2) * UnramifiedWhittaker.placeEmbed ℚ p (x j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
          Wf (RSCarrier.finFactor ((RSCarrier.finFactor g : G2) * UnramifiedWhittaker.placeEmbed ℚ p (x j))) := by

  have hτc : ∀ j, Continuous fun z : G2 =>
      (((detNorm (z * UnramifiedWhittaker.placeEmbed ℚ p (x j))) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        φ (z * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA) := by
    intro j
    refine Continuous.mul ?_ (hφ.comp ((continuous_mul_const _).mul continuous_const))
    refine Continuous.cpow ?_ continuous_const fun z => ?_
    · exact Complex.continuous_ofReal.comp (continuous_detNorm.comp (continuous_mul_const _))
    · exact Complex.ofReal_mem_slitPlane.2 (detNorm_pos _)
  rw [W_finsum D χ hχ c _ hτc g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_

  have ha : ∀ (y : 𝔸) (z : G2),
      (fun z : G2 => (((detNorm (z * UnramifiedWhittaker.placeEmbed ℚ p (x j))) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) (unipotentGL2 y * z) =
        (fun z : G2 => (((detNorm (z * UnramifiedWhittaker.placeEmbed ℚ p (x j))) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) z := by
    intro y z
    show (((detNorm (unipotentGL2 y * z * UnramifiedWhittaker.placeEmbed ℚ p (x j))) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = _
    rw [mul_assoc, detNorm_unipotentGL2_mul]
  rw [W_mul_invariant D χ (fun z : G2 => (((detNorm (z * UnramifiedWhittaker.placeEmbed ℚ p (x j))) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))
    (fun z : G2 => φ (z * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA)) ha g]

  rw [show (fun z : G2 => φ (z * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA)) =
      fun z : G2 => φ (z * (UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA)) from funext fun z => by rw [mul_assoc],
    W_translate D χ φ _ g, hWAf]

  have hx := placeEmbed_mem_fin p (x j)
  rw [ratArchGL2_mul, ratArchGL2_mul, ratArchGL2_placeEmbed, ratArchGL2_archRealGLAt, one_mul]
  rw [show g * (UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA) = g * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA from
      (mul_assoc _ _ _).symm, finFactor_mul_archRealGLAt, finFactor_mul_of_mem g hx,
    detNorm_cpow_eq_archAbs_cpow_mul_finNorm_cpow, ratArchGL2_mul, ratArchGL2_placeEmbed, mul_one,
    finFactor_mul_of_mem g hx, coe_finFactor_of_mem (mul_mem (RSCarrier.finFactor g).2 hx)]
  ring

end Ws23Iso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end Ws23RefA2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23RefA3

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
p2m_open "LanglandsTunnell LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction~det_upperUnipotent3 NumberField.AdelicLevel NumberField.AdelicVolume"
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws23Iso

local notation "G2" => AdelicGL2 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

theorem whittakerCoefficient_translates_archTranslate (D : Set G2) (χ : AddChar 𝔸 ℂ) (hχ : Continuous χ)
    (φ : G2 → ℂ) (hφ : Continuous φ) (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ g : G2, whittakerCoefficient ℚ (pinsQ D) χ φ 1 g = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g))
    (p : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (c : Fin n → ℂ) (x : Fin n → GL (Fin 2) (p.adicCompletion ℚ))
    (hA : GL (Fin 2) ℝ) (g : G2) :
    whittakerCoefficient ℚ (pinsQ D) χ
        (fun g : G2 => ∑ j, c j * φ (g * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA)) 1 g =
      WA (ratArchGL2 g * hA) *
        ∑ j, c j * Wf (RSCarrier.finFactor ((RSCarrier.finFactor g : G2) * UnramifiedWhittaker.placeEmbed ℚ p (x j))) := by
  have hτc : ∀ j, Continuous fun z : G2 => φ (z * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA) :=
    fun j => hφ.comp ((continuous_mul_const _).mul continuous_const)
  rw [W_finsum D χ hχ c _ hτc g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx := placeEmbed_mem_fin p (x j)
  rw [show (fun z : G2 => φ (z * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA)) =
      fun z : G2 => φ (z * (UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA)) from funext fun z => by rw [mul_assoc],
    W_translate D χ φ _ g, hWAf, ratArchGL2_mul, ratArchGL2_mul, ratArchGL2_placeEmbed, ratArchGL2_archRealGLAt, one_mul,
    show g * (UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA) = g * UnramifiedWhittaker.placeEmbed ℚ p (x j) * ιR hA from
      (mul_assoc _ _ _).symm, finFactor_mul_archRealGLAt, finFactor_mul_of_mem g hx]
  ring

theorem archComponent3_iota (g : G2) :
    archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ g) = iotaGL (glArch (𝓞 ℚ) ℚ g) :=
  map_iotaGL (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) g

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem rsLocalIntegral_rpow_neg_half_mul (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ)
    (hδ : ∀ g, δ g ≠ 0) (s : ℂ) (W F : G → ℂ) :
    RSCarrier.rsLocalIntegral μ H μH δ s (fun g => ((δ g : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * W g) F =
      RSCarrier.rsLocalIntegral μ H μH δ (s - 1 / 2) W F := by
  unfold RSCarrier.rsLocalIntegral
  congr 1
  funext g
  have h0 : ((δ g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hδ g)
  rw [show (s - 1 / 2 - 1 / 2 : ℂ) = -(1 / 2) + (s - 1 / 2) by ring, Complex.cpow_add _ _ h0]
  ring

theorem rsLocalIntegral_const_mul_right (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ) (s : ℂ)
    (c : ℂ) (W F : G → ℂ) :
    RSCarrier.rsLocalIntegral μ H μH δ s W (fun g => c * F g) = c * RSCarrier.rsLocalIntegral μ H μH δ s W F := by
  unfold RSCarrier.rsLocalIntegral
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

theorem indicator_mul_weight {X : Type*} (S : Set X) (a W : X → ℂ) :
    S.indicator (fun x => a x * W x) = fun x => a x * S.indicator W x := by
  funext x
  by_cases hx : x ∈ S
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

end Ws23Iso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end Ws23RefA3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23HLKit
open IsDedekindDomain NumberField Matrix AutomorphicForm LanglandsTunnell
open NumberField.AdelicLevel AdelicDock UnramifiedWhittaker

noncomputable section

namespace Ws23TH

theorem ratArchGL2_mul (g k : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * k) = ratArchGL2 g * ratArchGL2 k := by
  unfold LanglandsTunnell.ratArchGL2
  rw [map_mul, map_mul, map_mul]

theorem ratArchGL2_coe (k : finiteAdelicGL2Subgroup ℚ) : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, map_one, map_one]

theorem finFactor_mul_coe (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : finiteAdelicGL2Subgroup ℚ) :
    RSCarrier.finFactor (g * k) = RSCarrier.finFactor g * k := by
  apply Subtype.ext
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 (g * ↑k)))⁻¹ * (g * ↑k) =
    (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g * ↑k
  rw [ratArchGL2_mul, ratArchGL2_coe, mul_one, mul_assoc]

theorem placeEmbed_mul_eq_mul_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ))
    (k : finiteAdelicGL2Subgroup ℚ) (hk : localAt ℚ p (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) :
    placeEmbed ℚ p y * (k : AdelicGL2 (𝓞 ℚ) ℚ) = (k : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p y := by
  have hArch : glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p y) = 1 := glArch_finEmbed ..
  have hFin : glFin (𝓞 ℚ) ℚ (placeEmbed ℚ p y) = localEmbed (𝓞 ℚ) ℚ p y := glFin_finEmbed ..
  have hkp : (finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
      (((glFin (𝓞 ℚ) ℚ (k : AdelicGL2 (𝓞 ℚ) ℚ)) : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    have h : ((localAt ℚ p (k : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = 1 := by
      rw [hk, Units.val_one]
    exact h
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hArch, one_mul, mul_one]
  · rw [map_mul, map_mul, hFin]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_localEmbed]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = p
    · subst hw
      rw [mapMatrix_localMat_self, hkp, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ p _ hw, mul_one, one_mul]

end Ws23TH
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

namespace Ws23Iso
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell UnramifiedWhittaker

theorem psiLoc_psiQ_eq_psiV (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.CubicInduction.psiLoc NumberField.StandardAddChar.psiQ v = NumberField.StandardAddChar.psiV v := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  show NumberField.StandardAddChar.psiQ (NumberField.StandardAddChar.adeleSingleAt ℚ v x) = _
  rw [show NumberField.StandardAddChar.adeleSingleAt ℚ v x =
      ((0 : InfiniteAdeleRing ℚ), NumberField.StandardAddChar.finAdeleSingleAt ℚ v x) from rfl,
    NumberField.StandardAddChar.psiQ_apply]
  simp only
  rw [AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply]
  rw [finprod_eq_single (fun w => NumberField.StandardAddChar.psiV w (NumberField.StandardAddChar.finAdeleSingleAt ℚ v x w)) v]
  · rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_self]
  · intro w hw
    rw [NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v x hw]
    exact AddChar.map_zero_eq_one _

theorem localAt_placeEmbed_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (h : p ≠ q) (x : GL (Fin 2) (q.adicCompletion ℚ)) :
    localAt ℚ p (placeEmbed ℚ q x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ q x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ q x h]

end Ws23Iso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

p2m_open "LanglandsTunnell.CubicInduction~det_upperUnipotent3" in open LanglandsTunnell.RankinSelberg MeasureTheory in
open scoped Classical in

theorem Ws23Iso.supply_heckeLocal
    (Φ : HeckeEigensystem ℚ ℂ) (SQ S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (hSQ1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ φ)
    (WA : GL (Fin 2) ℝ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (RSCarrier.finFactor g))
    (hWne : whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 ≠ 0)
    [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ)) :
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ p x * Wf (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              Wf (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = Wf (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, Wf (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repSome
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
            Wf (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repInf
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            Φ.a p * Wf (RSCarrier.finFactor g)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.scalarPi
            (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf (RSCarrier.finFactor g)) := by
  have key := fun (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ SQ) =>
    LanglandsTunnell.finWhittaker_unipotent_levelOne_hecke_centre_of_isIsotypicCuspFormAt
      (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) R.centralChar Φ.level S Φ φ hiso WA Wf
      hWAf hWne p (fun h' => hp (hS h')) (fun h' => hp (hSQ1 p h')) (ϖ p) (hπ p hp) (hϖ p hp)
  refine ⟨fun p hp x g => ?_, fun p hp => (key p hp).2.1, fun p hp => (key p hp).2.2.1,
    fun p hp => (key p hp).2.2.2⟩
  rw [Ws23Iso.psiLoc_psiQ_eq_psiV]
  exact (key p hp).1 x g

p2m_open "LanglandsTunnell.CubicInduction~det_upperUnipotent3" in open LanglandsTunnell.RankinSelberg MeasureTheory in
open scoped Classical in

theorem Ws23Iso.finWhittaker_mul_right_unipotent_levelOne_hecke_centre_of_localAt_eq_one
    (Φ : HeckeEigensystem ℚ ℂ) (SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (Wf₀ : finiteAdelicGL2Subgroup ℚ → ℂ) (h : finiteAdelicGL2Subgroup ℚ)
    (hh : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → localAt ℚ p (h : AdelicGL2 (𝓞 ℚ) ℚ) = 1)
    (h1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf₀ (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ p x * Wf₀ (RSCarrier.finFactor g))
    (h2 : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x)) = Wf₀ (RSCarrier.finFactor g))
    (h3 : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ S', ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repSome
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))))) +
            Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repInf
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            Φ.a p * Wf₀ (RSCarrier.finFactor g))
    (h4 : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ S', ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.scalarPi
            (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)))) =
            (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf₀ (RSCarrier.finFactor g)) :
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ∀ (x : p.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf₀ (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.unipotent x) * g) * h) =
            psiLoc NumberField.StandardAddChar.psiQ p x * Wf₀ (RSCarrier.finFactor g * h)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' →
          ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ →
              Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p x) * h) =
                Wf₀ (RSCarrier.finFactor g * h)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ S', ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repSome
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp)
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ p.asIdeal)))))) * h)) +
            Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.repInf
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp))) * h) =
            Φ.a p * Wf₀ (RSCarrier.finFactor g * h)) ∧
        (∀ p : HeightOneSpectrum (𝓞 ℚ), ∀ hp : p ∉ S', ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf₀ (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ p (UnramifiedWhittaker.scalarPi
            (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπ p hp))) * h) =
            (Φ.b p / (Ideal.absNorm p.asIdeal : ℂ)) * Wf₀ (RSCarrier.finFactor g * h)) := by
  have hcomm : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ∀ (y : GL (Fin 2) (p.adicCompletion ℚ))
      (g : AdelicGL2 (𝓞 ℚ) ℚ),
      g * UnramifiedWhittaker.placeEmbed ℚ p y * (h : AdelicGL2 (𝓞 ℚ) ℚ) =
        g * (h : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p y := fun p hp y g => by
    rw [mul_assoc, Ws23TH.placeEmbed_mul_eq_mul_placeEmbed p y h (hh p fun hq => hp (hSS' hq)), ← mul_assoc]
  have hff : ∀ X : AdelicGL2 (𝓞 ℚ) ℚ,
      RSCarrier.finFactor X * h = RSCarrier.finFactor (X * (h : AdelicGL2 (𝓞 ℚ) ℚ)) := fun X =>
    (Ws23TH.finFactor_mul_coe X h).symm
  refine ⟨fun p hp x g => ?_, fun p hp x g hx => ?_, fun p hp g => ?_, fun p hp g => ?_⟩
  · rw [hff, hff, mul_assoc]
    exact h1 p hp x (g * (h : AdelicGL2 (𝓞 ℚ) ℚ))
  · rw [hff, hff, hcomm p hp]
    exact h2 p hp x (g * (h : AdelicGL2 (𝓞 ℚ) ℚ)) hx
  · simp_rw [hff, hcomm p hp]
    exact h3 p hp (g * (h : AdelicGL2 (𝓞 ℚ) ℚ))
  · rw [hff, hff, hcomm p hp]
    exact h4 p hp (g * (h : AdelicGL2 (𝓞 ℚ) ℚ))

end Ws23HLKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

namespace Ws23N2Glue

theorem exists_fin_sum_of_mem_span_translates_gen {G : Type*} [Mul G] (f w : G → ℂ)
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => f (g * h))) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → G), w = fun y => ∑ i, c i * f (y * x i) := by
  classical
  refine Submodule.span_induction (p := fun w _ => ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → G),
      w = fun y => ∑ i, c i * f (y * x i)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨h, rfl⟩
    exact ⟨1, fun _ => 1, fun _ => h, by funext y; simp⟩
  · exact ⟨0, Fin.elim0, Fin.elim0, by funext y; simp⟩
  · rintro u u' - - ⟨n, c, x, rfl⟩ ⟨n', c', x', rfl⟩
    refine ⟨n + n', Fin.append c c', Fin.append x x', ?_⟩
    funext y
    rw [Pi.add_apply, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · rintro a u - ⟨n, c, x, rfl⟩
    refine ⟨n, fun i => a * c i, x, ?_⟩
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Ws23N2Glue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23AwaySkelHelpers

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3"
open scoped Matrix

namespace Ws23Iso

theorem isClosed_range_unipotentGL2Hom {K : Type*} [Field K] [TopologicalSpace K] [T1Space K] :
    IsClosed (Set.range (unipotentGL2Hom (R := K)) : Set (GL (Fin 2) K)) := by
  have hS : (Set.range (unipotentGL2Hom (R := K)) : Set (GL (Fin 2) K)) =
      {g : GL (Fin 2) K | (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1} := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [unipotentGL2Hom, unipotentGL2_coe]
    · rintro ⟨h00, h10, h11⟩
      refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K) 0 1), ?_⟩
      refine Units.ext ?_
      show ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) K) 0 1) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
      rw [unipotentGL2_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  rw [hS]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) K)).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

section GL3
variable {A : Type*} [CommRing A] {R : Type*} [CommRing R]

theorem det_upperUnipotent3 (x y z : A) : Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Units.val_one, Matrix.det_fin_three]
  simp

theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace (ψ : AddChar A R) {W W' : GL (Fin 3) A → R}
    (hW : IsGL3PsiWhittakerFn ψ W) (h : W' ∈ gl3CyclicSubspace W) : IsGL3PsiWhittakerFn ψ W' := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace A R ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', rfl⟩
    show IsGL3PsiWhittakerFn ψ (gl3AmbientRightTranslate h' W)
    intro x y z g
    rw [gl3AmbientRightTranslate_apply, gl3AmbientRightTranslate_apply, mul_assoc]
    exact hW x y z (g * h')
  exact hle h

theorem isGL3PsiWhittakerFn_twist (ψ : AddChar A R) {W : GL (Fin 3) A → R}
    (hW : IsGL3PsiWhittakerFn ψ W) (c : Aˣ → R) :
    IsGL3PsiWhittakerFn ψ (fun g => c (Matrix.GeneralLinearGroup.det g) * W g) := by
  intro x y z g
  show c (Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z * g)) * W (upperUnipotent3 x y z * g) = _
  rw [map_mul, det_upperUnipotent3, one_mul, hW]
  ring

end GL3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

open NumberField.StandardAddChar in
theorem psiLocal_mul_psiLoc (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = psiQ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (t : p.adicCompletion ℚ) :
    psiLocal ℚ p t * psiLoc ψ p t = 1 := by
  rw [psiLocal_rat_eq_psiQ_adeleSingleAt, ← hψQ, AddChar.inv_apply]
  show ψ (-(adeleSingleAt ℚ p t)) * ψ (adeleSingleAt ℚ p t) = 1
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

open NumberField.StandardAddChar in
theorem psiLocal_inv_eq_psiLoc (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψQ : ψ⁻¹ = psiQ)
    (p : HeightOneSpectrum (𝓞 ℚ)) : (psiLocal ℚ p)⁻¹ = psiLoc ψ p := by
  refine AddChar.ext _ _ fun t => ?_
  rw [AddChar.inv_apply]
  have h1 := psiLocal_mul_psiLoc ψ hψQ p (-t)
  have h2 : psiLoc ψ p (-t) * psiLoc ψ p t = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc psiLocal ℚ p (-t) = psiLocal ℚ p (-t) * (psiLoc ψ p (-t) * psiLoc ψ p t) := by rw [h2, mul_one]
    _ = (psiLocal ℚ p (-t) * psiLoc ψ p (-t)) * psiLoc ψ p t := by ring
    _ = psiLoc ψ p t := by rw [h1, one_mul]

theorem exists_open_subgroup_localChar_eq_one {χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ}
    (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ U₀ : Subgroup (v.adicCompletion ℚ)ˣ, IsOpen (U₀ : Set (v.adicCompletion ℚ)ˣ) ∧
      ∀ u ∈ U₀, NumberField.TateGlobal.localChar χA v u = 1 := by
  obtain ⟨n, hn⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ v
    (NumberField.TateGlobal.localChar χA v) (NumberField.TateGlobal.continuous_localChar χA hχA.2.1 v)
  refine ⟨(NumberField.TateGlobal.localChar χA v).ker, ?_, fun u hu => (MonoidHom.mem_ker).mp hu⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp (-((n : ℤ) + 1)))
  have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := by
    rw [ha]; exact zero_lt_iff.mpr WithZero.exp_ne_zero
  have hO1 : IsOpen {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
    have h := (NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v
    convert h using 1
    rfl
  have hball : IsOpen {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))} := by
    have hset : {x : v.adicCompletion ℚ | Valued.v (x - 1) ≤ WithZero.exp (-((n : ℤ) + 1))} =
        (fun x => a⁻¹ * (x - 1)) ⁻¹' {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.map_mul, map_inv₀, ← ha]
      rw [inv_mul_le_iff₀ hpos, mul_one]
    rw [hset]
    exact hO1.preimage (continuous_const.mul (continuous_id.sub continuous_const))
  have hU : IsOpen {u : (v.adicCompletion ℚ)ˣ |
      Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))} :=
    hball.preimage Units.continuous_val
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · show Valued.v (((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))
    rw [Units.val_one, sub_self, map_zero]; exact zero_le'
  intro u hu
  have hu' : Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) := hu
  have hlt : Valued.v ((u : v.adicCompletion ℚ) - 1) < 1 :=
    lt_of_le_of_lt hu' (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv1 : Valued.v (u : v.adicCompletion ℚ) = 1 := by
    have e : (u : v.adicCompletion ℚ) = 1 + ((u : v.adicCompletion ℚ) - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  have hmem : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v n :=
    ⟨hv1, Or.inr (hu'.trans (WithZero.exp_le_exp.mpr (by omega)))⟩
  exact (MonoidHom.mem_ker).mpr (hn.1 u hmem)

theorem unipotent_det_eq_one {K : Type*} [Field K] (x : K) :
    Matrix.GeneralLinearGroup.det (UnramifiedWhittaker.unipotent x) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  show Matrix.det !![(1 : K), x; 0, 1] = 1
  simp [Matrix.det_fin_two_of]

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem rsLocalIntegral_mul_rpow_neg_half (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ)
    (hδ : ∀ g, δ g ≠ 0) (s : ℂ) (W F : G → ℂ) :
    RSCarrier.rsLocalIntegral μ H μH δ s W (fun g => ((δ g : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * F g) =
      RSCarrier.rsLocalIntegral μ H μH δ (s - 1 / 2) W F := by
  unfold RSCarrier.rsLocalIntegral
  congr 1
  funext g
  have h0 : ((δ g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hδ g)
  rw [show (s - 1 / 2 - 1 / 2 : ℂ) = -(1 / 2) + (s - 1 / 2) by ring, Complex.cpow_add _ _ h0]
  ring

end Ws23Iso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end Ws23AwaySkelHelpers
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23LocConst
namespace Ws23Iso

theorem continuous_of_forall_mul_mem_eq {G X : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [TopologicalSpace X] (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → X)
    (hf : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) : Continuous f := by
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, (isOpenMap_mul_left g) _ hU, ⟨1, U.one_mem, mul_one g⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  show f (g * k) ∈ s
  rw [hf k hk g]; exact hg
end Ws23Iso
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"
end Ws23LocConst
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23FinNZLemmas

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg NumberField.AdelicLevel"

noncomputable section

namespace Ws23FinNZ

theorem exists_localHaar_families (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (μv : ∀ v : HeightOneSpectrum (𝓞 ℚ), @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
      (μNv : ∀ v : HeightOneSpectrum (𝓞 ℚ),
        @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v))),
      ∀ v ∈ SQ, (letI := localGLBorel ℚ v; haveI := borelSpace_localGLBorel ℚ v;
        (μv v).IsHaarMeasure ∧ (μNv v).IsHaarMeasure) := by
  refine ⟨fun v => by
      letI := localGLBorel ℚ v; haveI := borelSpace_localGLBorel ℚ v; haveI := locallyCompactSpace_localGL ℚ v
      exact Measure.haar,
    fun v => by
      letI := localGLBorel ℚ v; haveI := borelSpace_localGLBorel ℚ v; haveI := locallyCompactSpace_localGL ℚ v
      haveI : LocallyCompactSpace ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range :=
        (Ws23Iso.isClosed_range_unipotentGL2Hom (K := v.adicCompletion ℚ)).locallyCompactSpace
      exact Measure.haar,
    fun v _ => ?_⟩
  letI := localGLBorel ℚ v; haveI := borelSpace_localGLBorel ℚ v; haveI := locallyCompactSpace_localGL ℚ v
  haveI : LocallyCompactSpace ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range :=
    (Ws23Iso.isClosed_range_unipotentGL2Hom (K := v.adicCompletion ℚ)).locallyCompactSpace
  exact ⟨inferInstance, inferInstance⟩

theorem not_countable_halfPlane (σ : ℝ) : ¬ Set.Countable {s : ℂ | σ < s.re} := by
  intro hcnt
  have hpre := hcnt.preimage Complex.ofReal_injective
  have hset : ((fun x : ℝ => (x : ℂ)) ⁻¹' {s : ℂ | σ < s.re}) = Set.Ioi σ := by
    ext x; simp [Complex.ofReal_re]
  rw [hset] at hpre
  have h := Cardinal.le_aleph0_iff_set_countable.2 hpre
  rw [Cardinal.mk_Ioi_real] at h
  exact lt_irrefl _ (h.trans_lt Cardinal.aleph0_lt_continuum)

theorem purified_eq_norm_mul (p : HeightOneSpectrum (𝓞 ℚ)) {nP : ℕ} (cP : Fin nP → ℂ)
    (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ)) (Wf0 : finiteAdelicGL2Subgroup ℚ → ℂ) (gf : finiteAdelicGL2Subgroup ℚ) :
    (∑ j, cP j * (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
          ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
          Wf0 (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) *
        ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
          Wf0 (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold detNorm
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le (NumberField.TateGlobal.ideleNorm_pos _).le]
  ring

theorem exists_open_stabiliser_sum_translate (p : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → GL (Fin 2) (p.adicCompletion ℚ)) (u : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hu : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), u (g * k) = u g) :
    ∃ U' : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U' : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k' ∈ U', ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        (∑ j, c j * u (g * k' * x j)) = ∑ j, c j * u (g * x j) := by
  obtain ⟨U, hUo, hU⟩ := hu
  refine ⟨⨅ j : Fin n, (U.comap (MulAut.conj (x j)⁻¹).toMonoidHom), ?_, ?_⟩
  · rw [Subgroup.coe_iInf]
    refine isOpen_iInter_of_finite fun j => ?_
    have hcont : Continuous fun w : GL (Fin 2) (p.adicCompletion ℚ) => (x j)⁻¹ * w * x j :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hset : ((U.comap (MulAut.conj (x j)⁻¹).toMonoidHom : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
          Set (GL (Fin 2) (p.adicCompletion ℚ))) =
        (fun w : GL (Fin 2) (p.adicCompletion ℚ) => (x j)⁻¹ * w * x j) ⁻¹' (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
      ext w
      simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, SetLike.mem_coe,
        MulAut.conj_apply, inv_inv]
    rw [hset]
    exact hUo.preimage hcont
  · intro k' hk' g
    refine Finset.sum_congr rfl fun j _ => ?_
    have hkj : (x j)⁻¹ * k' * x j ∈ U := by
      have := (Subgroup.mem_iInf.1 hk') j
      rw [Subgroup.mem_comap] at this
      simpa [MulAut.conj_apply] using this
    have e : g * k' * x j = g * x j * ((x j)⁻¹ * k' * x j) := by group
    rw [e, hU _ hkj (g * x j)]

end Ws23FinNZ
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

end Ws23FinNZLemmas
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23FinNZLemmas2
open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell LanglandsTunnell.CubicInduction~det_upperUnipotent3 LanglandsTunnell.RankinSelberg NumberField.AdelicLevel"
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
noncomputable section
namespace Ws23FinNZ

theorem rsFinIntegral_indicator_purified_shift [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μfH : Measure (finiteAdelicGL2Subgroup ℚ)) (μNF : Measure RSCarrier.finUnipotent)
    (S : Set (finiteAdelicGL2Subgroup ℚ)) (p : HeightOneSpectrum (𝓞 ℚ)) {nP : ℕ} (cP : Fin nP → ℂ)
    (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ)) (Wf0 : finiteAdelicGL2Subgroup ℚ → ℂ)
    (Ff : finiteAdelicGL2Subgroup ℚ → ℂ) (s : ℂ) :
    RSCarrier.rsFinIntegral μfH μNF s
        (S.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
          (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
              ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
            Wf0 (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))))
          (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) Ff =
      RSCarrier.rsFinIntegral μfH μNF (s - 1 / 2)
        (S.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
          (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
            Wf0 (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))))
          (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) Ff := by
  unfold RSCarrier.rsFinIntegral
  have hδ : ∀ g : finiteAdelicGL2Subgroup ℚ,
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ≠ 0 := fun g =>
    (NumberField.TateGlobal.ideleNorm_pos _).ne'
  rw [← Ws23Iso.rsLocalIntegral_rpow_neg_half_mul _ _ _ _ hδ s, ← Ws23Iso.indicator_mul_weight]
  congr 2
  funext g
  beta_reduce
  rw [Ws23Iso.finFactor_coe]
  exact Ws23FinNZ.purified_eq_norm_mul p cP xP Wf0 g

end Ws23FinNZ
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"
end Ws23FinNZLemmas2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Ws23PE3Sec

open IsDedekindDomain NumberField Matrix
p2m_open "LanglandsTunnell.CubicInduction~det_upperUnipotent3 NumberField.AdelicLevel AdelicDock"

noncomputable section

namespace Ws23PE3

section Generic

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem matrix3_eq_of_forall_mapMatrix_finAdeleEval_eq {M N : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)}
    (h : ∀ w : HeightOneSpectrum R,
      (AdelicLevel.finAdeleEval R K w).mapMatrix M = (AdelicLevel.finAdeleEval R K w).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply] using hw

theorem matrix3_eq_of_mapMatrix_arch_fin_eq {M N : Matrix (Fin 3) (Fin 3) (AdeleRing R K)}
    (h₁ : (AdelicLevel.adeleArch R K).mapMatrix M = (AdelicLevel.adeleArch R K).mapMatrix N)
    (h₂ : (AdelicLevel.adeleFin R K).mapMatrix M = (AdelicLevel.adeleFin R K).mapMatrix N) :
    M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

variable (v : HeightOneSpectrum R)

def localMat3 (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K) :=
  Matrix.of fun i j => splice R K v ((1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) i j) (g i j)

theorem localMat3_apply_self (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) (i j : Fin 3) :
    localMat3 R K v g i j v = g i j := by
  simp [localMat3]

theorem localMat3_apply_of_ne (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) (i j : Fin 3)
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    localMat3 R K v g i j w = (1 : Matrix (Fin 3) (Fin 3) (w.adicCompletion K)) i j := by
  simp only [localMat3, Matrix.of_apply, splice_apply_of_ne R K v _ _ hw]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mapMatrix_localMat3_self (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    (AdelicLevel.finAdeleEval R K v).mapMatrix (localMat3 R K v g) = g := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply, localMat3_apply_self]

theorem mapMatrix_localMat3_of_ne (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion K))
    {w : HeightOneSpectrum R} (hw : w ≠ v) :
    (AdelicLevel.finAdeleEval R K w).mapMatrix (localMat3 R K v g) = 1 := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply,
    localMat3_apply_of_ne R K v g i j hw]

theorem localMat3_one : localMat3 R K v 1 = 1 := by
  refine matrix3_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [mapMatrix_localMat3_self, map_one]
  · rw [mapMatrix_localMat3_of_ne R K v _ hw, map_one]

theorem localMat3_mul (g h : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) :
    localMat3 R K v (g * h) = localMat3 R K v g * localMat3 R K v h := by
  refine matrix3_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, mapMatrix_localMat3_self, mapMatrix_localMat3_self, mapMatrix_localMat3_self]
  · rw [map_mul, mapMatrix_localMat3_of_ne R K v _ hw, mapMatrix_localMat3_of_ne R K v _ hw,
      mapMatrix_localMat3_of_ne R K v _ hw, mul_one]

def localEmbed3 : GL (Fin 3) (v.adicCompletion K) →* GL (Fin 3) (FiniteAdeleRing R K) where
  toFun g :=
    { val := localMat3 R K v g
      inv := localMat3 R K v ((g⁻¹ : GL (Fin 3) (v.adicCompletion K)) : Matrix _ _ _)
      val_inv := by rw [← localMat3_mul, Units.mul_inv, localMat3_one]
      inv_val := by rw [← localMat3_mul, Units.inv_mul, localMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact localMat3_one R K v)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact localMat3_mul R K v _ _)

@[scoped simp] theorem coe_localEmbed3 (g : GL (Fin 3) (v.adicCompletion K)) :
    ((localEmbed3 R K v g : GL (Fin 3) (FiniteAdeleRing R K)) : Matrix _ _ _) = localMat3 R K v g := rfl

def finMat3 (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) : Matrix (Fin 3) (Fin 3) (AdeleRing R K) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)

theorem mapMatrix_arch_finMat3 (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (finMat3 R K g) = 1 := by
  ext i j
  simp [finMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_finMat3 (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (finMat3 R K g) = g := by
  ext i j
  simp [finMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem finMat3_one : finMat3 R K 1 = 1 :=
  matrix3_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_finMat3, map_one])
    (by rw [mapMatrix_fin_finMat3, map_one])

theorem finMat3_mul (g h : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing R K)) :
    finMat3 R K (g * h) = finMat3 R K g * finMat3 R K h :=
  matrix3_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_finMat3, mapMatrix_arch_finMat3, mapMatrix_arch_finMat3, mul_one])
    (by rw [map_mul, mapMatrix_fin_finMat3, mapMatrix_fin_finMat3, mapMatrix_fin_finMat3])

def finEmbed3 : GL (Fin 3) (FiniteAdeleRing R K) →* AdelicGL 3 R K where
  toFun g :=
    { val := finMat3 R K g
      inv := finMat3 R K ((g⁻¹ : GL (Fin 3) (FiniteAdeleRing R K)) : Matrix _ _ _)
      val_inv := by rw [← finMat3_mul, Units.mul_inv, finMat3_one]
      inv_val := by rw [← finMat3_mul, Units.inv_mul, finMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact finMat3_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact finMat3_mul R K _ _)

@[scoped simp] theorem coe_finEmbed3 (g : GL (Fin 3) (FiniteAdeleRing R K)) :
    ((finEmbed3 R K g : AdelicGL 3 R K) : Matrix _ _ _) = finMat3 R K g := rfl

def placeEmbed3 : GL (Fin 3) (v.adicCompletion K) →* AdelicGL 3 R K :=
  (finEmbed3 R K).comp (localEmbed3 R K v)

theorem componentAt3_placeEmbed3_self (g : GL (Fin 3) (v.adicCompletion K)) :
    componentAt3 R K v (placeEmbed3 R K v g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.finAdeleEval R K v) ((AdelicLevel.adeleFin R K) (finMat3 R K (localMat3 R K v g) i j)) = _
  rw [AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply]
  simp only [finMat3, Matrix.of_apply]
  exact localMat3_apply_self R K v g i j

theorem componentAt3_placeEmbed3_of_ne (g : GL (Fin 3) (v.adicCompletion K)) {w : HeightOneSpectrum R}
    (hw : w ≠ v) : componentAt3 R K w (placeEmbed3 R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.finAdeleEval R K w) ((AdelicLevel.adeleFin R K) (finMat3 R K (localMat3 R K v g) i j)) = _
  rw [AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply, Units.val_one]
  simp only [finMat3, Matrix.of_apply]
  exact localMat3_apply_of_ne R K v g i j hw

theorem archComponent3_placeEmbed3 (g : GL (Fin 3) (v.adicCompletion K)) :
    archComponent3 R K (placeEmbed3 R K v g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change (AdelicLevel.adeleArch R K) (finMat3 R K (localMat3 R K v g) i j) = _
  rw [AdelicLevel.adeleArch_apply, Units.val_one]
  simp only [finMat3, Matrix.of_apply]

theorem ext3 {x y : AdelicGL 3 R K} (harch : archComponent3 R K x = archComponent3 R K y)
    (hfin : ∀ w : HeightOneSpectrum R, componentAt3 R K w x = componentAt3 R K w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have h := congrArg
      (fun u : GL (Fin 3) (InfiniteAdeleRing K) => (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing K)) i j) harch
    exact h
  · refine RestrictedProduct.ext _ _ fun w => ?_
    have h := congrArg
      (fun u : GL (Fin 3) (w.adicCompletion K) => (u : Matrix (Fin 3) (Fin 3) (w.adicCompletion K)) i j) (hfin w)
    exact h

theorem placeEmbed3_commute {v w : HeightOneSpectrum R} (hvw : v ≠ w) (g : GL (Fin 3) (v.adicCompletion K))
    (h : GL (Fin 3) (w.adicCompletion K)) : Commute (placeEmbed3 R K v g) (placeEmbed3 R K w h) := by
  refine ext3 R K ?_ fun u => ?_
  · rw [map_mul, map_mul, archComponent3_placeEmbed3, archComponent3_placeEmbed3]
  · rw [map_mul, map_mul]
    by_cases huv : u = v
    · subst huv
      rw [componentAt3_placeEmbed3_self, componentAt3_placeEmbed3_of_ne R K w h hvw, mul_one, one_mul]
    · by_cases huw : u = w
      · subst huw
        rw [componentAt3_placeEmbed3_self, componentAt3_placeEmbed3_of_ne R K v g huv, mul_one, one_mul]
      · rw [componentAt3_placeEmbed3_of_ne R K v g huv, componentAt3_placeEmbed3_of_ne R K w h huw]

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

section Family

variable (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

theorem famComm (x : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) :
    ((Finset.univ : Finset ↥SQ) : Set ↥SQ).Pairwise
      (Function.onFun Commute fun p : ↥SQ => placeEmbed3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (x p)) :=
  fun p _ q _ hpq => placeEmbed3_commute (𝓞 ℚ) ℚ (fun h => hpq (Subtype.ext h)) (x p) (x q)

def famProd (x : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  (Finset.univ : Finset ↥SQ).noncommProd
    (fun p : ↥SQ => placeEmbed3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (x p)) (famComm SQ x)

theorem archComponent3_famProd (x : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) :
    archComponent3 (𝓞 ℚ) ℚ (famProd SQ x) = 1 := by
  unfold famProd
  rw [Finset.map_noncommProd,
    Finset.noncommProd_eq_pow_card _ _ _ 1 (fun p _ => archComponent3_placeEmbed3 (𝓞 ℚ) ℚ _ _), one_pow]

theorem componentAt3_famProd_of_not_mem (x : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ SQ) : componentAt3 (𝓞 ℚ) ℚ v (famProd SQ x) = 1 := by
  unfold famProd
  rw [Finset.map_noncommProd,
    Finset.noncommProd_eq_pow_card _ _ _ 1 (fun p _ =>
      componentAt3_placeEmbed3_of_ne (𝓞 ℚ) ℚ _ _ (fun h => hv (by rw [h]; exact p.2))), one_pow]

theorem componentAt3_famProd_self (x : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))) (p : ↥SQ) :
    componentAt3 (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (famProd SQ x) = x p := by
  classical
  unfold famProd
  rw [Finset.map_noncommProd, ← Finset.noncommProd_erase_mul _ (Finset.mem_univ p),
    Finset.noncommProd_eq_pow_card _ _ _ 1 (fun q hq =>
      componentAt3_placeEmbed3_of_ne (𝓞 ℚ) ℚ _ _
        (fun h => Finset.ne_of_mem_erase hq (Subtype.ext h).symm)),
    one_pow, one_mul, componentAt3_placeEmbed3_self]

theorem componentAt3_famProd_of_mem (x : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ SQ) : componentAt3 (𝓞 ℚ) ℚ v (famProd SQ x) = x ⟨v, hv⟩ :=
  componentAt3_famProd_self SQ x ⟨v, hv⟩

end Family
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso"

open scoped Classical in

theorem exists_adelicGL3_components
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ))
    (κ : ∀ v' : ↥(SQ.erase p), LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ))) :
    ∃ h₃f : AdelicGL 3 (𝓞 ℚ) ℚ,
      archComponent3 (𝓞 ℚ) ℚ h₃f = 1 ∧ componentAt3 (𝓞 ℚ) ℚ p h₃f = 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) ∧
      ∀ v' : ↥(SQ.erase p), componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f = κ v' := by
  classical
  refine ⟨famProd (SQ.erase p) κ, archComponent3_famProd _ κ,
    componentAt3_famProd_of_not_mem _ κ (Finset.notMem_erase p SQ),
    fun v hv => componentAt3_famProd_of_not_mem _ κ (fun h => hv (Finset.mem_of_mem_erase h)),
    fun v' => componentAt3_famProd_self _ κ v'⟩

end Ws23PE3
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23PE3"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23PE3"

end Ws23PE3Sec
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23PE3"

section Ws23S5Sec

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker AdelicDock NumberField.AdelicLevel

namespace Ws23S5

theorem placeEmbed_mul_comm (p : HeightOneSpectrum (𝓞 ℚ)) {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : localAt ℚ p g = 1)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x * g = g * placeEmbed ℚ p x := by
  have hgp : (finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := congrArg Units.val hg
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x) * _ = _ * finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x)
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = p
    · subst hw
      rw [hgp, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ p _ hw, one_mul, mul_one]

theorem sum_translate_mul_eq
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
    (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    {m : ℕ} (w : ∀ v : ↥SQ, Fin m → GL (Fin 2) ((v : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
    (W' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hWK : ∀ (α : Fin m) (k : finiteAdelicGL2Subgroup ℚ),
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' α g)
    (hsplitW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      Wf (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ v : ↥SQ, w v α (localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g)
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (x : ι → GL (Fin 2) (p.adicCompletion ℚ))
    (k : finiteAdelicGL2Subgroup ℚ)
    (hk1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
      localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (hk2 : ∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1)
    (g : finiteAdelicGL2Subgroup ℚ) :
    ∑ j, c j * Wf (RSCarrier.finFactor (((g * k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j))) =
      ∑ j, c j * Wf (RSCarrier.finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j))) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcomm : ((g * k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j) =
      ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j)) * (k : AdelicGL2 (𝓞 ℚ) ℚ) := by
    rw [Subgroup.coe_mul, mul_assoc, ← placeEmbed_mul_comm p (hk2 p hp) (x j), mul_assoc]
  have hloc : ∀ v : ↥SQ, localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) (((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j)) * (k : AdelicGL2 (𝓞 ℚ) ℚ)) =
      localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j)) := fun v => by
    rw [map_mul, hk2 (v : HeightOneSpectrum (𝓞 ℚ)) v.2, mul_one]
  have hWf : Wf (RSCarrier.finFactor (((g * k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j))) =
      Wf (RSCarrier.finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (x j))) := by
    rw [hcomm, hsplitW, hsplitW]
    exact Finset.sum_congr rfl fun α _ => by
      rw [hWK α k hk1 hk2, Finset.prod_congr rfl fun v _ => by rw [hloc v]]
  rw [hWf]

end Ws23S5
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23PE3"

end Ws23S5Sec
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23PE3"

namespace Ws23S14

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open NumberField.AdelicLevel UnramifiedWhittaker LanglandsTunnell.RankinSelberg

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ

theorem localAt_apply' (w : HeightOneSpectrum (𝓞 ℚ)) (g : G2) (i j : Fin 2) :
    (localAt ℚ w g : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 w := rfl

theorem localAt_placeEmbed_self' (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ v (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne' (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ))
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) : localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem glArch_placeEmbed' (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    glArch (𝓞 ℚ) ℚ (placeEmbed ℚ v x) = 1 :=
  AdelicDock.glArch_finEmbed _ _ _

theorem ext_of_glArch_of_localAt' {g h : G2} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hl : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v g = localAt ℚ v h) : g = h := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrFun (congrFun (congrArg (fun M : GL (Fin 2) (InfiniteAdeleRing ℚ) =>
      (M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))) ha) i) j
    rw [glArch_apply, glArch_apply] at this
    exact this
  · refine RestrictedProduct.ext _ _ fun v => ?_
    have := congrFun (congrFun (congrArg (fun M : GL (Fin 2) (v.adicCompletion ℚ) =>
      (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) (hl v)) i) j
    rw [localAt_apply', localAt_apply'] at this
    exact this

theorem inv_mul_placeEmbed_mul' (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2) :
    g⁻¹ * placeEmbed ℚ v x * g = placeEmbed ℚ v ((localAt ℚ v g)⁻¹ * x * localAt ℚ v g) := by
  refine ext_of_glArch_of_localAt' ?_ fun u => ?_
  · rw [map_mul, map_mul, map_inv, glArch_placeEmbed', glArch_placeEmbed', mul_one, inv_mul_cancel]
  · by_cases hu : u = v
    · subst hu
      rw [map_mul, map_mul, map_inv, localAt_placeEmbed_self', localAt_placeEmbed_self']
    · rw [map_mul, map_mul, map_inv, localAt_placeEmbed_of_ne' v _ hu, localAt_placeEmbed_of_ne' v _ hu, mul_one,
        inv_mul_cancel]

theorem left_blind_of_right_blind' {W : G2 → ℂ} {v : HeightOneSpectrum (𝓞 ℚ)}
    (h : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2), W (g * placeEmbed ℚ v x) = W g)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2) : W (placeEmbed ℚ v x * g) = W g := by
  have e : placeEmbed ℚ v x * g = g * (g⁻¹ * placeEmbed ℚ v x * g) := by group
  rw [e, inv_mul_placeEmbed_mul', h]

theorem apply_mul_eq_of_blind' {W : G2 → ℂ} (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (h : ∀ v ∈ T, ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : G2), W (g * placeEmbed ℚ v x) = W g) :
    ∀ (e : G2), glArch (𝓞 ℚ) ℚ e = 1 → (∀ u, u ∉ T → localAt ℚ u e = 1) →
      ∀ g : G2, W (g * e) = W g ∧ W (e * g) = W g := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro e he hl g
    have : e = 1 := ext_of_glArch_of_localAt' (by rw [he, map_one]) fun u => by
      rw [hl u (Finset.notMem_empty u), map_one]
    rw [this, mul_one, one_mul]
    exact ⟨rfl, rfl⟩
  | @insert v T hvT ih =>
    intro e he hl g
    set e' : G2 := e * placeEmbed ℚ v (localAt ℚ v e)⁻¹ with he'
    have he'a : glArch (𝓞 ℚ) ℚ e' = 1 := by rw [he', map_mul, he, glArch_placeEmbed', one_mul]
    have he'l : ∀ u, u ∉ T → localAt ℚ u e' = 1 := by
      intro u hu
      by_cases huv : u = v
      · subst huv; rw [he', map_mul, localAt_placeEmbed_self', mul_inv_cancel]
      · rw [he', map_mul, localAt_placeEmbed_of_ne' v _ huv, mul_one]
        exact hl u (fun hh => (Finset.mem_insert.1 hh).elim huv hu)
    have hdec : e = e' * placeEmbed ℚ v (localAt ℚ v e) := by
      rw [he', mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    have ih' := ih (fun u hu => h u (Finset.mem_insert_of_mem hu)) e' he'a he'l
    have hv := h v (Finset.mem_insert_self v T)
    refine ⟨?_, ?_⟩
    · rw [hdec, ← mul_assoc, hv, (ih' g).1]
    · rw [hdec, mul_assoc, (ih' _).2, left_blind_of_right_blind' hv]

section Carrier
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem rsLocalIntegral_comm (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ) (s : ℂ) (W F : G → ℂ) :
    RSCarrier.rsLocalIntegral μ H μH δ s W F = RSCarrier.rsLocalIntegral μ H μH δ s F W := by
  unfold RSCarrier.rsLocalIntegral
  congr 1
  funext g
  rw [mul_comm (W g) (F g)]

theorem rsLocalIntegral_finset_sum_right (μ : Measure G) (H : Subgroup G) (μH : Measure H) (δ : G → ℝ) (s : ℂ)
    (W : G → ℂ) {ι : Type*} (T : Finset ι) (e : ι → ℂ) (f : ι → G → ℂ)
    (hint : ∀ i ∈ T, Integrable (fun g : G => (f i g * W g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
      (μ.withDensity (HaarQuotient.density H μH))) :
    RSCarrier.rsLocalIntegral μ H μH δ s W (fun g => ∑ i ∈ T, e i * f i g) =
      ∑ i ∈ T, e i * RSCarrier.rsLocalIntegral μ H μH δ s W (f i) := by
  unfold RSCarrier.rsLocalIntegral
  have hpt : ∀ g : G, (W g * ∑ i ∈ T, e i * f i g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2) =
      ∑ i ∈ T, e i * ((f i g * W g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) := by
    intro g
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finset_sum T fun i hi => (hint i hi).const_mul (e i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  ring

end Carrier
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23PE3"

theorem cpow_ne_zero_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y ≠ 0 :=
  fun h => hx ((Complex.cpow_eq_zero_iff x y).1 h).1

theorem modulus_det_cpow_ne_zero {Kv : Type*} [Field Kv] [TopologicalSpace Kv] [IsTopologicalRing Kv] [LocallyCompactSpace Kv]
    (g : GL (Fin 2) Kv) (y : ℂ) :
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : Kvˣ) : Kv) : ℝ) : ℂ) ^ y ≠ 0 :=
  cpow_ne_zero_of_ne_zero (Complex.ofReal_ne_zero.2 (NNReal.coe_ne_zero.2
    (LanglandsTunnell.TateLocal.modulus_ne_zero (Units.ne_zero _)))) y

theorem exists_tuple_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {m : ℕ}
    (A U P : Fin m → ℂ) (Qb : ι → Fin m → ℂ) (Q : ∀ i : ι, Fin m → Fin (n i) → ℂ) (e : ∀ i : ι, Fin (n i) → ℂ)
    (Wv : ι → Fin m → ℂ) (cp Mp : ℂ) (cv M : ι → ℂ)
    (S : (∀ i, Fin (n i)) → ℂ) (hS : ∀ t, S t = ∑ β, A β * (P β * ∏ i, Q i β (t i)))
    (hlin : ∀ i β, Qb i β = ∑ j, e i j * Q i β j)
    (hP : ∀ β, P β = cp * (Mp * U β)) (hQb : ∀ i β, Qb i β = cv i * (M i * Wv i β))
    (hcp : cp ≠ 0) (hMp : Mp ≠ 0) (hcv : ∀ i, cv i ≠ 0) (hM : ∀ i, M i ≠ 0)
    (hB : ∑ β, A β * (U β * ∏ i, Wv i β) ≠ 0) : ∃ t : (∀ i, Fin (n i)), S t ≠ 0 := by
  classical
  have key : ∑ t : (∀ i, Fin (n i)), (∏ i, e i (t i)) * S t = ∑ β, A β * (P β * ∏ i, Qb i β) := by
    have h1 : ∀ β, (∏ i, Qb i β) = ∑ t : (∀ i, Fin (n i)), ∏ i, (e i (t i) * Q i β (t i)) := by
      intro β
      simp_rw [hlin]
      rw [Finset.prod_univ_sum]
      simp only [Fintype.piFinset_univ]
    simp_rw [h1, Finset.mul_sum, hS, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  have hval : ∑ β, A β * (P β * ∏ i, Qb i β) = (cp * Mp * ∏ i, (cv i * M i)) * ∑ β, A β * (U β * ∏ i, Wv i β) := by
    simp_rw [hP, hQb, Finset.prod_mul_distrib]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  have hne : ∑ t : (∀ i, Fin (n i)), (∏ i, e i (t i)) * S t ≠ 0 := by
    rw [key, hval]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hcp hMp)
      (Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hcv i) (hM i))) hB
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨t, (mul_ne_zero_iff.1 ht).2⟩

end Ws23S14
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23Iso P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch.Ws23PE3"

set_option maxHeartbeats 4000000 in
open MeasureTheory LanglandsTunnell.TateLocal in

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSQ : (∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ) ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ SQ →
        Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Φ.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Φ.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hSK : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∈ SK ↔ 𝔓.under (𝓞 ℚ) ∈ SQ)
    (P : RealArchParam)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : S ⊆ SQ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral) (hRc : Continuous R.toFun)
    (Cfin : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hRS : R.exceptionalSet ⊆ S)
    (hP1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (hP2 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (hRcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Wr : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℂ → ℂ)
    (kw : (InfinitePlace ℚ → ZMod 2) → InfinitePlace ℚ → ℤ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (hφKf : ∀ par, ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ (φv par) α = φv par)
    (hφarch : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (kw par w)) (φv par))
    (hkw1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w))
    (hkw2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hφW : ∀ par, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (φv par) 1 (diagOne a * g)
          = (∏ w : InfinitePlace ℚ, Wr par w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
              * Cfin (a : AdeleRing (𝓞 ℚ) ℚ).2 g)
    (hWr1 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par w ∨ b = par w + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (Tq : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωT : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓)
    (hE : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∈ Tq → 𝔓 ∈ SK)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hoff : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hdepth : ∀ w : ↥SK,
      4 * (FractionalIdeal.count K w.1
            ((Φ.level.map (algebraMap (𝓞 ℚ) (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) +
          LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w.1) + 1) ≤
        LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1))
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → IsUnramifiedCharAt χA v)
    (kχ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hkχ : ∀ p ∈ SQ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (NumberField.TateGlobal.localChar χA p) (kχ p))
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (c₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hν : ∀ p ∈ SQ, ∀ w ∈ primeFibre ℚ K p, ∃ c : ℕ, c ≤ c₀ p ∧
      LanglandsTunnell.TateLocal.HasConductorExponentAt K w
        (NumberField.TateGlobal.localChar
          (μ * (χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)⁻¹) w) c)
    (bQ : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hbQ : ∀ p ∈ SQ, p.asIdeal ^ bQ p ∣ Φ.level ∧ ¬ p.asIdeal ^ (bQ p + 1) ∣ Φ.level)
    (hkfloor : ∀ p ∈ SQ,
      6 * ((bQ p : ℤ) + 3 * (2 * ((∑ᶠ w ∈ primeFibre ℚ K p,
              ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                    (2 * ((52 : ℤ) + 3 * (c₀ p : ℤ)) +
                      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                  (c₀ p : ℤ) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
            ((52 : ℤ) + 3 * (c₀ p : ℤ)))) + 3) + 7 ≤ (kχ p : ℤ))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hνadm : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (hμν : μ = ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
    (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (hcR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (hcC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hψQ : ψ⁻¹ = NumberField.StandardAddChar.psiQ)
    (F : CubicInductionForm K (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ ν)
    (hF0 : F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
        F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K ν) v (F.whittakerLoc v))
    (hFc : Continuous F.form) (hFw : Continuous F.whittaker) (hFdw : Continuous F.dualWhittaker)
    (hFg : IsGaugeMajorised3 ℚ F.whittaker) (hFdg : IsGaugeMajorised3 ℚ F.dualWhittaker)
    (hBad :
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K ν v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K ν v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W))
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')
    (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (mP : ∀ p : ↥SQ, LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)
    (hmPmem : ∀ p : ↥SQ, mP p ∈ gl3CyclicSubspace
      (fun g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (p : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (p : HeightOneSpectrum (𝓞 ℚ)) g))
    (hmP1 : ∀ p : ↥SQ, mP p 1 = 1)
    (hW₃admM : ∀ p : ↥SQ, ∀ Uv : Subgroup (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)))) →
      ∃ B : Finset (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ), ∀ W ∈ gl3CyclicSubspace (mP p),
        (∀ k ∈ Uv, ∀ g : LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 (p : HeightOneSpectrum (𝓞 ℚ)) → ℂ)))
    (hW₃irrM : ∀ p : ↥SQ, ∀ W ∈ gl3CyclicSubspace (mP p), W ≠ 0 → mP p ∈ gl3CyclicSubspace W)
    (hμf : finiteAdelicGL2Subgroup ℚ)
    (hhμf : (hμf : AdelicGL2 (𝓞 ℚ) ℚ) =
      ((S' \ SQ).toList.map (fun p => if hp : p ∉ SQ then
          UnramifiedWhittaker.placeEmbed ℚ p
            ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p))
              (hπ p hp)) ^ (-(inducedLevelAt K μ p : ℤ)))
        else 1)).prod)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (hWfC : ∀ par (g : finiteAdelicGL2Subgroup ℚ), Wf par g = Cfin 1 (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hWf1 : ∀ par, Wf par 1 ≠ 0)
    (hV : ∀ par, ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ SQ →
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))
    (w₀ : GL (Fin 2) ℚ) (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1; 1, 0])
    (Wfd : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWfd : ∀ par (gf : finiteAdelicGL2Subgroup ℚ), Wfd par gf =
      ((NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (gf : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) *
        Wf par (RSCarrier.finFactor (globalPoints (𝓞 ℚ) ℚ w₀ * transposeInvN (Fin 2) (gf : AdelicGL2 (𝓞 ℚ) ℚ))))
    (par : InfinitePlace ℚ → ZMod 2) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ SQ)
    (w₂b : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂b : w₂b ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par))

    (nP : ℕ) (cP : Fin nP → ℂ) (xP : Fin nP → GL (Fin 2) (p.adicCompletion ℚ))
    (hnd : ∃ gf : finiteAdelicGL2Subgroup ℚ,
      (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) gf ≠ 0) :

    ∀ (μfH : MeasureTheory.Measure (finiteAdelicGL2Subgroup ℚ)) [μfH.IsHaarMeasure]
      (μNF : MeasureTheory.Measure RSCarrier.finUnipotent) [μNF.IsHaarMeasure],
    ∃ (h₃f : AdelicGL 3 (𝓞 ℚ) ℚ), archComponent3 (𝓞 ℚ) ℚ h₃f = 1 ∧ componentAt3 (𝓞 ℚ) ℚ p h₃f = 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) ∧
    ∃ (m : ℕ) (d : Fin m → ℂ) (k : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) ∧
    ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧
        RSCarrier.rsFinIntegral μfH μNF s

          ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ))))

          ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ≠ 0} := by
  classical
  intro μfH _ μNF _
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo ℚ

  obtain ⟨μv, μNv, hμv⟩ : ∃ (μv : ∀ v : HeightOneSpectrum (𝓞 ℚ), @Measure (GL (Fin 2) (v.adicCompletion ℚ)) (localGLBorel ℚ v))
      (μNv : ∀ v : HeightOneSpectrum (𝓞 ℚ),
        @Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range (@Subtype.instMeasurableSpace _ _ (localGLBorel ℚ v))),
      ∀ v ∈ SQ, (letI := localGLBorel ℚ v; haveI := borelSpace_localGLBorel ℚ v;
        (μv v).IsHaarMeasure ∧ (μNv v).IsHaarMeasure) := by
    exact Ws23FinNZ.exists_localHaar_families SQ

  obtain ⟨mS, w, W', hwmem, hblind, hwlaw, hWlaw, hwmeas, hWmeas, hwsm, hwlev, hWK, hindep, hsplitW⟩ :=
    AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
      Φ SQ hSQ.1 S R φv hiso hφne WA Wf hWAf par (hV par)

  have hwmeasL : ∀ (v : ↥SQ) (α : Fin mS), (letI := localGLBorel ℚ (v : HeightOneSpectrum (𝓞 ℚ)); Measurable (w v α)) := by
    intro v α
    letI := localGLBorel ℚ (v : HeightOneSpectrum (𝓞 ℚ)); haveI := borelSpace_localGLBorel ℚ (v : HeightOneSpectrum (𝓞 ℚ))
    obtain ⟨U, hUo, hU⟩ := hwsm v α
    exact (Ws23Iso.continuous_of_forall_mul_mem_eq U hUo _ hU).measurable
  have hmPsmW : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g := by
    intro v
    by_cases hbad : IsBadPlace K ν v
    · exact (hBad {v}).1 v (Finset.mem_singleton_self v) hbad
    · refine ⟨localMaximalCompact3 (𝓞 ℚ) ℚ v, ?_, fun k hk g => (F.spherical v hbad).1 g k hk⟩

      have hO : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
        have h := (NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v
        convert h using 1
        rfl
      have hc1 : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
        fun i j => (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))).matrix_elem i j
      have hc2 : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v =>
          ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
        fun i j => ((Units.continuous_val (M := Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))).comp
          continuous_inv).matrix_elem i j
      have hset : ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
          (⋂ i, ⋂ j, (fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹'
              {x : v.adicCompletion ℚ | Valued.v x ≤ 1}) ∩
          (⋂ i, ⋂ j, (fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹'
              {x : v.adicCompletion ℚ | Valued.v x ≤ 1}) := by
        ext k
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
        exact Iff.rfl
      rw [hset]
      exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (hc1 i j)).inter
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (hc2 i j))
  have hFwL : ∀ v : HeightOneSpectrum (𝓞 ℚ), Continuous (F.whittakerLoc v) := by
    intro v
    obtain ⟨Uv, hUvo, hUv⟩ := (hmPsmW v)
    exact Ws23Iso.continuous_of_forall_mul_mem_eq Uv hUvo _ hUv

  obtain ⟨cE, hcE0, hCE⟩ :=
    LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsFinIntegral_indicator_purified_eq_mul_sum_prod_rsLocalIntegral
      K _hdeg SQ hSQ.2 χA hχA hχoff ν hνadm ψ hψ hψQ hlev F hF0 hFwL p hp (Wf par) mS w W' hblind hwlaw hWlaw hwmeasL hWmeas hwsm hWK
      hsplitW nP cP xP μfH μNF μv μNv hμv

  haveI hIfin : ∀ p' : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p'.asIdeal) := fun p' =>
    @Fintype.ofFinite _ (Ideal.finiteQuotientOfFreeOfNeBot p'.asIdeal p'.ne_bot)
  have hbev : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → Φ.b v ≠ 0 := fun v hv h0 => by
    have := hb v hv; rw [h0, norm_zero] at this; exact zero_ne_one this

  have hWne := AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
    (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) R.centralChar Φ.level S Φ (φv par) (hiso par) (hφne par)
  have hHL0 := Ws23Iso.supply_heckeLocal Φ SQ S hS hSQ.1 R (φv par) (hiso par) (WA par) (Wf par) (hWAf par) hWne ϖ hπ hϖ
  have hHLj := fun j : Fin nP =>
    Ws23Iso.finWhittaker_mul_right_unipotent_levelOne_hecke_centre_of_localAt_eq_one Φ SQ SQ (Finset.Subset.refl _) ϖ hπ
      (Wf par) ⟨UnramifiedWhittaker.placeEmbed ℚ p (xP j), Ws23Iso.placeEmbed_mem_fin p (xP j)⟩
      (fun q hq => Ws23Iso.localAt_placeEmbed_of_ne (fun h => hq (by rw [h]; exact hp)) (xP j))
      hHL0.1 hHL0.2.1 hHL0.2.2.1 hHL0.2.2.2
  have hWfP : ∀ X : AdelicGL2 (𝓞 ℚ) ℚ,
      (∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor (((RSCarrier.finFactor X : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
          UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) =
      ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor X * ⟨UnramifiedWhittaker.placeEmbed ℚ p (xP j), Ws23Iso.placeEmbed_mem_fin p (xP j)⟩) := by
    intro X
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : RSCarrier.finFactor (((RSCarrier.finFactor X : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
        UnramifiedWhittaker.placeEmbed ℚ p (xP j)) =
        RSCarrier.finFactor X * ⟨UnramifiedWhittaker.placeEmbed ℚ p (xP j), Ws23Iso.placeEmbed_mem_fin p (xP j)⟩ := by
      have := Ws23TH.finFactor_mul_coe (((RSCarrier.finFactor X : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))
        ⟨UnramifiedWhittaker.placeEmbed ℚ p (xP j), Ws23Iso.placeEmbed_mem_fin p (xP j)⟩
      rw [Ws23Iso.finFactor_coe] at this
      exact this
    rw [e]
  have hHLp :         (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → ∀ (x : q.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ q x * (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ →
          ∀ (x : GL (Fin 2) (q.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤ →
              (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q x)) = (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repSome
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (q.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ q.asIdeal)))))))) +
            (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repInf
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            Φ.a q * (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.scalarPi
            (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            (Φ.b q / (Ideal.absNorm q.asIdeal : ℂ)) * (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor g)) := by
    refine ⟨fun q hq x g => ?_, fun q hq x g hx => ?_, fun q hq g => ?_, fun q hq g => ?_⟩
    · beta_reduce
      rw [hWfP, hWfP, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hHLj j).1 q hq x g]
      ring
    · beta_reduce
      rw [hWfP, hWfP]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hHLj j).2.1 q hq x g hx]
    · beta_reduce
      simp_rw [hWfP]
      rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum, ← mul_add, (hHLj j).2.2.1 q hq g]
      ring
    · beta_reduce
      rw [hWfP, hWfP, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hHLj j).2.2.2 q hq g]
      ring
  have hKp : ∀ k' : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k' : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k' : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : finiteAdelicGL2Subgroup ℚ, (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (g * k') = (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) g := by
    intro k' hk1 hk2 g
    beta_reduce
    exact Ws23S5.sum_translate_mul_eq SQ p hp (Wf par) w W' hWK hsplitW
      (fun j => cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) xP k' hk1 hk2 g
  have hneP : ∃ g : finiteAdelicGL2Subgroup ℚ, (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) g ≠ 0 := by
    obtain ⟨gf, hgf⟩ := hnd
    refine ⟨gf, fun h0 => hgf ?_⟩
    beta_reduce at h0 ⊢
    rw [Ws23FinNZ.purified_eq_norm_mul p cP xP (Wf par) gf, h0, mul_zero]
  obtain ⟨gS, hgS1, hgSne⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
      SQ ϖ hπ hϖ Φ.a Φ.b hbev (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) hHLp hKp hneP

  have hmPlaw : ∀ v : ↥SQ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ (v : HeightOneSpectrum (𝓞 ℚ)))⁻¹ (mP v) := by
    rintro ⟨v, hv⟩
    rw [Ws23Iso.psiLocal_inv_eq_psiLoc ψ hψQ v]
    exact Ws23Iso.isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace _
      (Ws23Iso.isGL3PsiWhittakerFn_twist _ (F.whittakerLoc_law v)
        (fun u => ((NumberField.TateGlobal.localChar χA v u : ℂˣ) : ℂ))) (hmPmem ⟨v, hv⟩)
  have hmPsm : ∀ v : ↥SQ, ∃ Uv : Subgroup (LocalGL3 (v : HeightOneSpectrum (𝓞 ℚ))), IsOpen (Uv : Set (LocalGL3 (v : HeightOneSpectrum (𝓞 ℚ)))) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 (v : HeightOneSpectrum (𝓞 ℚ)), mP v (g * k) = mP v g := by
    rintro ⟨v, hv⟩

    have hWsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g := by
      by_cases hbad : IsBadPlace K ν v
      · exact (hBad {v}).1 v (Finset.mem_singleton_self v) hbad
      · refine ⟨localMaximalCompact3 (𝓞 ℚ) ℚ v, ?_, fun k hk g => (F.spherical v hbad).1 g k hk⟩

        have hO : IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
          have h := (NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v
          convert h using 1
          rfl
        have hc1 : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
          fun i j => (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))).matrix_elem i j
        have hc2 : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v =>
            ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
          fun i j => ((Units.continuous_val (M := Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))).comp
            continuous_inv).matrix_elem i j
        have hset : ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
            (⋂ i, ⋂ j, (fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹'
                {x : v.adicCompletion ℚ | Valued.v x ≤ 1}) ∩
            (⋂ i, ⋂ j, (fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹'
                {x : v.adicCompletion ℚ | Valued.v x ≤ 1}) := by
          ext k
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
          exact Iff.rfl
        rw [hset]
        exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (hc1 i j)).inter
          (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (hc2 i j))

    obtain ⟨U₀, hU₀, hχU₀⟩ := Ws23Iso.exists_open_subgroup_localChar_eq_one hχA v
    obtain ⟨Ut, hUto, hUt⟩ := (LanglandsTunnell.CubicInduction.twist_det_localPackage v
      (LanglandsTunnell.CubicInduction.psiLoc ψ v) (NumberField.TateGlobal.localChar χA v) U₀ hU₀ hχU₀
      (fun z => hχA.2.2 _) (F.whittakerLoc v)).2.2.1 hWsm

    obtain ⟨m₀, d₀, kk, hmPeq⟩ := Ws23N2Glue.exists_fin_sum_of_mem_span_translates_gen
      (fun g : LocalGL3 v => ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        F.whittakerLoc v g) (mP ⟨v, hv⟩) (hmPmem ⟨v, hv⟩)

    refine ⟨⨅ j : Fin m₀, (Ut.comap (MulAut.conj (kk j)⁻¹).toMonoidHom), ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      refine isOpen_iInter_of_finite fun j => ?_
      have hcont : Continuous fun u : LocalGL3 v => (kk j)⁻¹ * u * kk j :=
        (continuous_const.mul continuous_id).mul continuous_const
      have hset : ((Ut.comap (MulAut.conj (kk j)⁻¹).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
          (fun u : LocalGL3 v => (kk j)⁻¹ * u * kk j) ⁻¹' (Ut : Set (LocalGL3 v)) := by
        ext u
        simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, SetLike.mem_coe,
          MulAut.conj_apply, inv_inv]
      rw [hset]
      exact hUto.preimage hcont
    · intro k hk g
      rw [hmPeq]
      show (∑ j, d₀ j * (((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det (g * k * kk j)) : ℂˣ) : ℂ) *
          F.whittakerLoc v (g * k * kk j))) =
        ∑ j, d₀ j * (((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det (g * kk j)) : ℂˣ) : ℂ) *
          F.whittakerLoc v (g * kk j))
      refine Finset.sum_congr rfl fun j _ => ?_
      have hkj : (kk j)⁻¹ * k * kk j ∈ Ut := by
        have := (Subgroup.mem_iInf.1 hk) j
        rw [Subgroup.mem_comap] at this
        simpa [MulAut.conj_apply] using this
      have e : g * k * kk j = g * kk j * ((kk j)⁻¹ * k * kk j) := by group
      rw [e]
      exact congrArg (d₀ j * ·) (hUt _ hkj (g * kk j))
  have hmPne : ∀ v : ↥SQ, mP v ≠ 0 := fun v h0 => by
    have := hmP1 v; rw [h0] at this; exact zero_ne_one this

  have hulaw : ∀ β ∈ (Finset.univ : Finset (Fin mS)), ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) g := by
    intro β _ x g
    beta_reduce
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (UnramifiedWhittaker.unipotent x) g (xP j), hwlaw ⟨p, hp⟩ β x (g * xP j)]
    ring
  have husm : ∀ β ∈ (Finset.univ : Finset (Fin mS)), ∃ U' : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (U' : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k' ∈ U', ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (g * k') = (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) g := by
    intro β _
    exact Ws23FinNZ.exists_open_stabiliser_sum_translate p _ xP (w ⟨p, hp⟩ β) (hwsm ⟨p, hp⟩ β)
  letI instMSp : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI := (hμv p hp).1
  haveI := (hμv p hp).2
  obtain ⟨W₃p, hW₃pmem, cp, hcp0, hbp⟩ :=
    LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
      p (mP ⟨p, hp⟩) (hmPlaw ⟨p, hp⟩) (hmPsm ⟨p, hp⟩) (hmPne ⟨p, hp⟩) (hW₃irrM ⟨p, hp⟩) (hW₃admM ⟨p, hp⟩)
      (localAt ℚ p (gS : AdelicGL2 (𝓞 ℚ) ℚ)) (Finset.univ : Finset (Fin mS))
      (fun β => (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j))) hulaw husm (μv p) (μNv p)

  obtain ⟨m₃, d, k, hk, hW₃pfam⟩ : ∃ (m₃ : ℕ) (d : Fin m₃ → ℂ) (k : Fin m₃ → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ j, archComponent3 (𝓞 ℚ) ℚ (k j) = 1 ∧
        ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ p → componentAt3 (𝓞 ℚ) ℚ v (k j) = 1) ∧
      W₃p = (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) := by
    have hle : gl3CyclicSubspace (mP ⟨p, hp⟩) ≤ gl3CyclicSubspace
        (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, rfl⟩
      exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace _ h (hmPmem ⟨p, hp⟩)
    obtain ⟨m₃, d, hloc, hW₃0⟩ := Ws23N2Glue.exists_fin_sum_of_mem_span_translates_gen
      (fun g : LocalGL3 p => ((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc p g)
      W₃p (hle hW₃pmem)
    choose kf hk1 hk2 hk3 using fun j : Fin m₃ =>
      LanglandsTunnell.CubicInduction.exists_adelicGL3_archComponent3_eq_one_componentAt3_eq ℚ p (hloc j)
    refine ⟨m₃, d, kf, fun j => ⟨hk1 j, hk3 j⟩, ?_⟩
    rw [hW₃0]
    funext y
    simp only [hk2]

  subst hW₃pfam

  have hBEv : ∀ v' : ↥(SQ.erase p),
      ∃ W₃ ∈ gl3CyclicSubspace (mP ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩), ∃ c : ℂ, c ≠ 0 ∧
        ∀ β ∈ (Finset.univ : Finset (Fin mS)), ∀ s : ℂ,
          (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
          haveI := borelSpace_localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
          Integrable (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
            ((fun g => W₃ (iotaGL g)) g * (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) g) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            ((μv (v' : HeightOneSpectrum (𝓞 ℚ))).withDensity (HaarQuotient.density (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))))) ∧
          (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
            RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ))
              s (fun g => W₃ (iotaGL g)) (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β)) =
            c * ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ)) :
                  (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) : ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2) *
              w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ)) := by
    intro v'
    letI : MeasurableSpace (GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)) := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
    haveI : BorelSpace (GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)) := borelSpace_localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
    haveI := (hμv (v' : HeightOneSpectrum (𝓞 ℚ)) (Finset.mem_of_mem_erase v'.2)).1
    haveI := (hμv (v' : HeightOneSpectrum (𝓞 ℚ)) (Finset.mem_of_mem_erase v'.2)).2
    exact LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_forall_rsLocalIntegral_eq_mul_apply_of_finite
      (v' : HeightOneSpectrum (𝓞 ℚ)) (mP ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩) (hmPlaw ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩) (hmPsm ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩) (hmPne ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩) (hW₃irrM ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩) (hW₃admM ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩)
      (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ)) (Finset.univ : Finset (Fin mS))
      (fun β => w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun β _ => hwlaw ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun β _ => hwsm ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
  choose W₃v hW₃vmem cv hcv0 hbv using hBEv

  have hexp : ∀ v' : ↥(SQ.erase p), ∃ (n : ℕ) (e : Fin n → ℂ) (κ : Fin n → LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ))),
      W₃v v' = fun y => ∑ i, e i * (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) (y * κ i) := by
    intro v'
    have hle : gl3CyclicSubspace (mP ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩) ≤ gl3CyclicSubspace (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, rfl⟩
      exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace _ h (hmPmem ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩)
    obtain ⟨n, e, κ, h⟩ := Ws23N2Glue.exists_fin_sum_of_mem_span_translates_gen (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) (W₃v v') (hle (hW₃vmem v'))
    exact ⟨n, e, κ, h⟩
  choose nv ev κv hW₃vexp using hexp

  have hIL : ∀ (v' : ↥(SQ.erase p)) (β : Fin mS) (i : Fin (nv v')), ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
      (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
          haveI := borelSpace_localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
          Integrable (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
            ((fun g => (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) (iotaGL g * κv v' i)) g * (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) g) *
              ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            ((μv (v' : HeightOneSpectrum (𝓞 ℚ))).withDensity (HaarQuotient.density (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))))) := by
    intro v' β i
    letI : MeasurableSpace (GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)) := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
    haveI : BorelSpace (GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)) := borelSpace_localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
    haveI := (hμv (v' : HeightOneSpectrum (𝓞 ℚ)) (Finset.mem_of_mem_erase v'.2)).1
    haveI := (hμv (v' : HeightOneSpectrum (𝓞 ℚ)) (Finset.mem_of_mem_erase v'.2)).2
    have hwspan : w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β ∈ Submodule.span ℂ {f : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) → ℂ |
        ∃ w₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (v' : HeightOneSpectrum (𝓞 ℚ)) (φv par),
          ∃ h : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ), f = fun g => w₀ (g * h)} :=
      Submodule.subset_span ⟨w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β, hwmem ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β, 1, funext fun g => by rw [mul_one]⟩
    have hW₃mem : (fun y : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) (y * κv v' i)) ∈ gl3CyclicSubspace (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) :=
      Submodule.subset_span ⟨κv v' i, funext fun y => by simp only [gl3AmbientRightTranslate_apply]⟩
    obtain ⟨σ₂, hσ₂⟩ :=
      LanglandsTunnell.RankinSelberg.exists_forall_integrable_iotaGL_mul_of_mem_span_localSpaceAt_of_mem_gl3CyclicSubspace_twist_of_finiteFamily_arch
        K _hdeg Φ SQ hSQ hb ha SK hSK P S hS R hRc Cfin hRS hP1 hP2 hRcen φv Wr kw hiso hφne hφKf hφarch hkw1 hkw2 hφW
      hWr1 hWr2 hWr3 hWr4 Tq ω hω hωT hE hωR hωC μ hμ hoff hdepth χA hχA hχoff kχ hkχ hχinf c₀ hν bQ hbQ hkfloor ν hνadm
      hμν uR aR uC kC hcR hcC ψ hψ hlev hψQ F hF0 hFc hFw hFdw hFg hFdg hBad S' hSS' hgood ϖ hπ hϖ mP hmPmem hmP1 hW₃admM
      hW₃irrM hμf hhμf WA Wf hWAf hWfC hWf1 hV w₀ hw₀ Wfd hWfd par (v' : HeightOneSpectrum (𝓞 ℚ)) (Finset.mem_of_mem_erase v'.2) (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) hwspan _ hW₃mem (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
    exact ⟨σ₂, hσ₂⟩
  choose σv hσv using hIL
  obtain ⟨σstar, hσstar⟩ : ∃ σstar : ℝ, ∀ v' β i, σv v' β i ≤ σstar := by
    obtain ⟨B, hB⟩ := (Set.range fun x : (Σ v' : ↥(SQ.erase p), Fin mS × Fin (nv v')) => σv x.1 x.2.1 x.2.2).toFinite.bddAbove
    exact ⟨B, fun v' β i => hB ⟨⟨v', (β, i)⟩, rfl⟩⟩

  obtain ⟨Ssingle, hSsingle⟩ : ∃ Ssingle : (∀ v' : ↥(SQ.erase p), Fin (nv v')) → ℂ → ℂ,
      ∀ t s, Ssingle t s = ∑ β : Fin mS, W' β 1 *
            ((letI := localGLBorel ℚ p;
            RSCarrier.rsLocalIntegral (μv p) (unipotentGL2Hom (R := (p).adicCompletion ℚ)).range (μNv p)
              (fun g : GL (Fin 2) ((p).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((p).adicCompletion ℚ)ˣ) :
                  (p).adicCompletion ℚ) : ℝ))
              s (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (fun y : GL (Fin 2) (p.adicCompletion ℚ) => (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL y))) *
              ∏ v' : ↥(SQ.erase p),
                (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
            RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ))
              s (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun g => (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) (iotaGL g * κv v' (t v'))))) := ⟨_, fun _ _ => rfl⟩
  have hClaim : ∀ s : ℂ, σstar < s.re → ∃ t : (∀ v' : ↥(SQ.erase p), Fin (nv v')), Ssingle t s ≠ 0 := by

    intro s hs
    classical
    have hgSarch : glArch (𝓞 ℚ) ℚ (gS : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 gS.2

    have hW'gS : ∀ α : Fin mS, W' α (gS : AdelicGL2 (𝓞 ℚ) ℚ) = W' α 1 := fun α => by
      have := (Ws23S14.apply_mul_eq_of_blind' SQ (fun v hv x g => hblind α ⟨v, hv⟩ x g)
        (gS : AdelicGL2 (𝓞 ℚ) ℚ) hgSarch hgS1 1).2
      rwa [mul_one] at this

    have hBeq : (∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        Wf par (RSCarrier.finFactor ((gS : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) =
        ∑ β : Fin mS, W' β 1 * ((fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (localAt ℚ p (gS : AdelicGL2 (𝓞 ℚ) ℚ)) *
          ∏ v' : ↥(SQ.erase p), w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β
            (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ))) := by
      have hterm : ∀ j, Wf par (RSCarrier.finFactor ((gS : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) =
          ∑ β : Fin mS, (w ⟨p, hp⟩ β (localAt ℚ p (gS : AdelicGL2 (𝓞 ℚ) ℚ) * xP j) *
            ∏ v' : ↥(SQ.erase p), w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β
              (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ))) * W' β 1 := by
        intro j
        rw [hsplitW]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [hblind β ⟨p, hp⟩ (xP j) (gS : AdelicGL2 (𝓞 ℚ) ℚ), hW'gS β]
        congr 1
        have hG : (∏ v : ↥SQ, w v β (localAt ℚ (v : HeightOneSpectrum (𝓞 ℚ)) ((gS : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) =
            ∏ u ∈ SQ, (if h : u ∈ SQ then w ⟨u, h⟩ β (localAt ℚ u ((gS : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) else (1 : ℂ)) := by
          rw [← Finset.prod_coe_sort SQ (fun u : HeightOneSpectrum (𝓞 ℚ) => if h : u ∈ SQ then
              w ⟨u, h⟩ β (localAt ℚ u ((gS : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) else (1 : ℂ))]
          exact Finset.prod_congr rfl fun v _ => by rw [dif_pos v.2]
        have hG' : (∏ v' : ↥(SQ.erase p), w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β
              (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ))) =
            ∏ u ∈ SQ.erase p, (if h : u ∈ SQ then w ⟨u, h⟩ β (localAt ℚ u ((gS : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) else (1 : ℂ)) := by
          rw [← Finset.prod_coe_sort (SQ.erase p)]
          refine Finset.prod_congr rfl fun v' _ => ?_
          rw [dif_pos (Finset.mem_of_mem_erase v'.2), map_mul,
            Ws23S14.localAt_placeEmbed_of_ne' p _ (Finset.ne_of_mem_erase v'.2), mul_one]
        rw [hG, ← Finset.mul_prod_erase SQ _ hp, dif_pos hp, map_mul, Ws23S14.localAt_placeEmbed_self', hG']
      simp_rw [hterm, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hB := hgSne
    beta_reduce at hB
    rw [hBeq] at hB

    refine Ws23S14.exists_tuple_ne_zero (ι := ↥(SQ.erase p)) (n := nv)
      (fun β => W' β 1)
      (fun β => (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (localAt ℚ p (gS : AdelicGL2 (𝓞 ℚ) ℚ)))
      (fun β => (letI := localGLBorel ℚ p;
            RSCarrier.rsLocalIntegral (μv p) (unipotentGL2Hom (R := (p).adicCompletion ℚ)).range (μNv p)
              (fun g : GL (Fin 2) ((p).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : ((p).adicCompletion ℚ)ˣ) :
                  (p).adicCompletion ℚ) : ℝ))
              s (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ∑ j, (cP j * (((detNorm (UnramifiedWhittaker.placeEmbed ℚ p (xP j)) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) * w ⟨p, hp⟩ β (y * xP j)) (fun y : GL (Fin 2) (p.adicCompletion ℚ) => (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL y))))
      (fun v' β => (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
            RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ))
              s (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun g => W₃v v' (iotaGL g))))
      (fun v' β j => (letI := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ));
            RSCarrier.rsLocalIntegral (μv (v' : HeightOneSpectrum (𝓞 ℚ))) (unipotentGL2Hom (R := ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)).range (μNv (v' : HeightOneSpectrum (𝓞 ℚ)))
              (fun g : GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) =>
                (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) :
                  ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ))
              s (w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β) (fun g => (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) (iotaGL g * κv v' j))))
      ev
      (fun v' β => w ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_of_mem_erase v'.2⟩ β
        (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ)))
      cp
      (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ p (gS : AdelicGL2 (𝓞 ℚ) ℚ)) :
          ((p).adicCompletion ℚ)ˣ) : (p).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
      cv
      (fun v' => ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det (localAt ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) (gS : AdelicGL2 (𝓞 ℚ) ℚ)) :
          (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)ˣ) : ((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
      (fun t => Ssingle t s) (fun t => hSsingle t s) ?_ ?_ ?_ hcp0 (Ws23S14.modulus_det_cpow_ne_zero _ _)
      hcv0 (fun v' => Ws23S14.modulus_det_cpow_ne_zero _ _) hB
    ·
      intro v' β
      letI : MeasurableSpace (GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)) := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
      haveI : BorelSpace (GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)) := borelSpace_localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
      beta_reduce
      rw [hW₃vexp v']
      exact Ws23S14.rsLocalIntegral_finset_sum_right _ _ _ _ s _ Finset.univ (ev v')
        (fun j => fun g => (fun g : LocalGL3 (v' : HeightOneSpectrum (𝓞 ℚ)) => ((NumberField.TateGlobal.localChar χA (v' : HeightOneSpectrum (𝓞 ℚ)) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * F.whittakerLoc (v' : HeightOneSpectrum (𝓞 ℚ)) g) (iotaGL g * κv v' j))
        (fun i _ => hσv v' β i s (lt_of_le_of_lt (hσstar v' β i) hs))
    ·
      intro β
      have h2 := (hbp β (Finset.mem_univ β) s).2
      beta_reduce at h2 ⊢
      rw [Ws23S14.rsLocalIntegral_comm, h2]
      ring
    ·
      intro v' β
      letI : MeasurableSpace (GL (Fin 2) (((v' : HeightOneSpectrum (𝓞 ℚ))).adicCompletion ℚ)) := localGLBorel ℚ (v' : HeightOneSpectrum (𝓞 ℚ))
      have h2 := (hbv v' β (Finset.mem_univ β) s).2
      beta_reduce at h2 ⊢
      rw [Ws23S14.rsLocalIntegral_comm, h2]
      ring

  have hhalf : ∀ σ'' : ℝ, ¬ Set.Countable {s : ℂ | σ'' < s.re} := by
    exact Ws23FinNZ.not_countable_halfPlane
  obtain ⟨tstar, htstar⟩ := Complex.exists_forall_not_countable_setOf_re_gt_mem_of_finite
    (fun t : (∀ v' : ↥(SQ.erase p), Fin (nv v')) => {s : ℂ | σstar < s.re ∧ Ssingle t s ≠ 0})
    (fun σ'' hcnt => hhalf (max σ'' σstar) (hcnt.mono fun s hs => by
      obtain ⟨t, ht⟩ := hClaim s (lt_of_le_of_lt (le_max_right _ _) hs)
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hs, t, lt_of_le_of_lt (le_max_right _ _) hs, ht⟩))

  obtain ⟨h₃f, hh₃fA, hh₃fp, hh₃foff, hh₃fat⟩ : ∃ h₃f : AdelicGL 3 (𝓞 ℚ) ℚ,
      archComponent3 (𝓞 ℚ) ℚ h₃f = 1 ∧ componentAt3 (𝓞 ℚ) ℚ p h₃f = 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → componentAt3 (𝓞 ℚ) ℚ v h₃f = 1) ∧
      ∀ v' : ↥(SQ.erase p), componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f = κv v' (tstar v') := by
    exact Ws23PE3.exists_adelicGL3_components SQ p fun v' => κv v' (tstar v')
  refine ⟨h₃f, hh₃fA, hh₃fp, hh₃foff, m₃, d, k, hk, fun σ' => ?_⟩

  have hkey : ∀ s : ℂ, σstar < (s - 1 / 2).re →
      (RSCarrier.rsFinIntegral μfH μNF s ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun gf : finiteAdelicGL2Subgroup ℚ => ∑ j, cP j *
            (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
                ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j))) : ℂ) ^ (-(1 / 2 : ℂ)) *
              Wf par (RSCarrier.finFactor ((gf : AdelicGL2 (𝓞 ℚ) ℚ) * UnramifiedWhittaker.placeEmbed ℚ p (xP j)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                  localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g : finiteAdelicGL2Subgroup ℚ =>
                (fun g : finiteAdelicGL2Subgroup ℚ =>
            (fun y : LocalGL3 p => ∑ j : Fin m₃, d j * (((NumberField.TateGlobal.localChar χA p (Matrix.GeneralLinearGroup.det (y * componentAt3 (𝓞 ℚ) ℚ p (k j))) : ℂˣ) : ℂ) * F.whittakerLoc p (y * componentAt3 (𝓞 ℚ) ℚ p (k j)))) (iotaGL (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) *
            (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              (if v = p then (1 : ℂ) else
                ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det
                    (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)) : ℂˣ) : ℂ) *
                  F.whittakerLoc v (componentAt3 (𝓞 ℚ) ℚ v (iota (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) * componentAt3 (𝓞 ℚ) ℚ v h₃f)))) (RSCarrier.finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ≠ 0 ↔ Ssingle tstar (s - 1 / 2) ≠ 0) := by
    intro s hs
    have hσs : ∀ v' β i, σv v' β i < (s - 1 / 2).re := fun v' β i => lt_of_le_of_lt (hσstar v' β i) hs
    have hce := hCE h₃f ⟨hh₃fA, hh₃fp, hh₃foff⟩ m₃ d k hk (s - 1 / 2)
      (fun β => (hbp β (Finset.mem_univ β) (s - 1 / 2)).1)
      (fun β v' hne => by
        have h3 : componentAt3 (𝓞 ℚ) ℚ (v' : HeightOneSpectrum (𝓞 ℚ)) h₃f =
            κv ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_erase.2 ⟨hne, v'.2⟩⟩
              (tstar ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_erase.2 ⟨hne, v'.2⟩⟩) :=
          hh₃fat ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_erase.2 ⟨hne, v'.2⟩⟩
        have hI := hσv ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_erase.2 ⟨hne, v'.2⟩⟩ β
          (tstar ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_erase.2 ⟨hne, v'.2⟩⟩) (s - 1 / 2)
          (hσs ⟨(v' : HeightOneSpectrum (𝓞 ℚ)), Finset.mem_erase.2 ⟨hne, v'.2⟩⟩ β _)
        rw [h3]
        exact hI)
    rw [Ws23FinNZ.rsFinIntegral_indicator_purified_shift, hce, hSsingle, mul_ne_zero_iff]
    have hX : ∀ (A B : ℂ), A = B → ((cE ≠ 0 ∧ A ≠ 0) ↔ B ≠ 0) := fun A B h => by
      subst h; exact ⟨And.right, fun h => ⟨hcE0, h⟩⟩
    refine hX _ _ ?_
    simp only [hh₃fat]
  intro hcnt
  refine htstar (σ' - 1 / 2) ?_
  have hpre := hcnt.preimage_of_injOn ((add_left_injective (1 / 2 : ℂ)).injOn)
  refine hpre.mono fun t ht => ?_
  obtain ⟨ht1, ht2, ht3⟩ := ht
  refine ⟨?_, ?_⟩
  · show σ' < (t + 1 / 2).re
    rw [Complex.add_re, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num]
    exact sub_lt_iff_lt_add.1 ht1
  · rw [hkey (t + 1 / 2) (by rw [add_sub_cancel_right]; exact ht2), add_sub_cancel_right]
    exact ht3

end S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_finTranslate_not_countable_rsFinIntegral_indicator_ne_zero_of_purifier_of_finiteFamily_arch (solution)
