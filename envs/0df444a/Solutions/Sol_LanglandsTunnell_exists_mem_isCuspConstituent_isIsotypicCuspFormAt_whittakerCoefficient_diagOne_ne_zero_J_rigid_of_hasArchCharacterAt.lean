-- Prove2me | solution 1 for LanglandsTunnell.exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d086ab90-0890-5063-882e-5fbfc1412119

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_AutomorphicForm_contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat
import Theorems.Thm_AutomorphicForm_exists_mem_principalIdeles_whittakerCoefficient_one_diagOne_mul_ne_zero
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_levelOne_rat
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AdelicDock LocalGL2 Rat.HeightOneSpectrum

namespace P2M
namespace Strip100

abbrev D0 : Set (AdelicGL2 (𝓞 ℚ) ℚ) := classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2

abbrev U0 : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) := fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ

abbrev gen0 : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ := fun v => heckeGen (𝓞 ℚ) ℚ v

theorem pins_eq : productionPinsGeneral ℚ = productionPinsOf ℚ D0 U0 gen0 (adelicBox ℚ) := rfl

theorem hcov_std : CoversModCentre ℚ
    (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
  AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat

abbrev w₀ : InfinitePlace ℚ := Rat.infinitePlace
theorem hw₀ : InfinitePlace.IsReal w₀ := Rat.isReal_infinitePlace

local notation "W1" => whittakerCoefficient ℚ (productionPinsOf ℚ D0 U0 gen0 (adelicBox ℚ)) NumberField.StandardAddChar.psiQ

section Glue

variable {F : Type} [Field F] [NumberField F]

theorem isHeckeCosetSystem_comp_equiv {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι ι' : Type*}
    {reps : ι → G} (e : ι' ≃ ι) (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset i := h.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective i j hij := e.injective (h.mk_injective hij)

theorem eq_of_parts_eq {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (h₂ : glFin (𝓞 F) F x = glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem eq_archPart_mul_finPart (g : AdelicGL2 (𝓞 F) F) :
    g = adelicArchGLIncl F (glArch (𝓞 F) F g) * finEmbed (𝓞 F) F (glFin (𝓞 F) F g) := by
  refine eq_of_parts_eq ?_ ?_
  · rw [map_mul, glArch_adelicArchGLIncl, glArch_finEmbed, mul_one]
  · rw [map_mul, glFin_adelicArchGLIncl, glFin_finEmbed, one_mul]

theorem finEmbed_mem_finiteAdelicGL2Subgroup (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finEmbed (𝓞 F) F k ∈ finiteAdelicGL2Subgroup F :=
  (mem_finiteAdelicGL2Subgroup_iff F _).mpr (glArch_finEmbed (𝓞 F) F k)

theorem coe_finComponent (w : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ((finComponent (𝓞 F) F w x : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))
      = (finAdeleEval (𝓞 F) F w).mapMatrix (x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
  ext i j
  rw [finComponent_apply, RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply]

theorem eq_of_forall_finComponent_eq {x y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w x = finComponent (𝓞 F) F w y) : x = y := by
  apply Units.ext
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
  rw [← coe_finComponent, ← coe_finComponent, h w]

theorem mul_finEmbed_localEmbed_comm (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL2 (𝓞 F) F)
    (hg : finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = 1) (m : GL (Fin 2) (v.adicCompletion F)) :
    g * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) * g := by
  refine eq_of_parts_eq ?_ ?_
  · rw [map_mul, map_mul, glArch_finEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, glFin_finEmbed]
    refine eq_of_forall_finComponent_eq fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hg, one_mul, mul_one]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F v m hw, one_mul, mul_one]

theorem mapMatrix_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    f.mapMatrix ((unipotentGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
      = ((unipotentGL2 (f x) : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) := by
  rw [unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

theorem coe_glFin (x : AdelicGL2 (𝓞 F) F) :
    ((glFin (𝓞 F) F x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
      = (adeleFin (𝓞 F) F).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j
  rw [glFin_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleFin_apply]

theorem coe_glArch (x : AdelicGL2 (𝓞 F) F) :
    ((glArch (𝓞 F) F x : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      = (adeleArch (𝓞 F) F).mapMatrix (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j
  rw [glArch_apply, RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply]

theorem unipotentInt_eq_unipotentGL2 (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletionIntegers F) :
    unipotentInt (R := v.adicCompletionIntegers F) (v.adicCompletion F) b
      = unipotentGL2 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) b) := by
  apply Units.ext
  rw [coe_unipotentInt, unipotentGL2_coe]

theorem finEmbed_localEmbed_unipotentInt (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletionIntegers F) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (unipotentInt (R := v.adicCompletionIntegers F) (v.adicCompletion F) b)) =
      unipotentGL2 (NumberField.StandardAddChar.adeleSingleAt F v
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) b)) := by
  set y : v.adicCompletion F := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) b with hy
  have h1 : adeleArch (𝓞 F) F (NumberField.StandardAddChar.adeleSingleAt F v y) = 0 := rfl
  have h2 : adeleFin (𝓞 F) F (NumberField.StandardAddChar.adeleSingleAt F v y)
      = NumberField.StandardAddChar.finAdeleSingleAt F v y := rfl
  refine eq_of_parts_eq ?_ ?_
  · rw [glArch_finEmbed]
    apply Units.ext
    rw [coe_glArch, mapMatrix_unipotentGL2, h1, unipotentGL2_zero]
  · rw [glFin_finEmbed]
    refine eq_of_forall_finComponent_eq fun w => ?_
    apply Units.ext
    rw [coe_finComponent w (glFin (𝓞 F) F _), coe_glFin, mapMatrix_unipotentGL2, mapMatrix_unipotentGL2, h2,
      finAdeleEval_apply]
    by_cases hw : w = v
    · subst hw
      rw [finComponent_localEmbed_self, NumberField.StandardAddChar.finAdeleSingleAt_apply_self,
        unipotentInt_eq_unipotentGL2]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F v _ hw,
        NumberField.StandardAddChar.finAdeleSingleAt_apply_of_ne F v y hw, unipotentGL2_zero]

theorem unipotentInt_mem_localLevelOne (v : HeightOneSpectrum (𝓞 F)) (N : Ideal (𝓞 F))
    (b : v.adicCompletionIntegers F) :
    unipotentInt (R := v.adicCompletionIntegers F) (v.adicCompletion F) b ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff]
  have key : ∀ c : v.adicCompletionIntegers F,
      IsLocalLevelOne (𝓞 F) F v N ((unipotentInt (R := v.adicCompletionIntegers F) (v.adicCompletion F) c :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) := by
    intro c
    rw [unipotentInt_eq_unipotentGL2, unipotentGL2_coe]
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]; exact one_mem _
      · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; exact c.2
      · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; exact zero_mem _
      · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]; exact one_mem _
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        map_zero]; exact zero_le'
    · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_self, map_zero]
      exact zero_le'
  refine ⟨key b, ?_⟩
  have hinv : (unipotentInt (R := v.adicCompletionIntegers F) (v.adicCompletion F) b)⁻¹
      = unipotentInt (R := v.adicCompletionIntegers F) (v.adicCompletion F) (-b) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, unipotentInt_eq_unipotentGL2, unipotentInt_eq_unipotentGL2, ← unipotentGL2_add,
      map_neg, neg_add_cancel, unipotentGL2_zero]
  rw [hinv]
  exact key (-b)

theorem finEmbed_localEmbed_unipotentInt_mem (v : HeightOneSpectrum (𝓞 F)) (N : Ideal (𝓞 F))
    (b : v.adicCompletionIntegers F) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (unipotentInt (R := v.adicCompletionIntegers F) (v.adicCompletion F) b))
      ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
  ⟨(finEmbed_mem_levelOne_iff (𝓞 F) F _).mpr
      ((localEmbed_mem_finiteLevelOne_iff (𝓞 F) F v _).mpr (unipotentInt_mem_localLevelOne v N b)),
    finEmbed_mem_finiteAdelicGL2Subgroup _⟩

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext; ext i j
  change algebraMap F (AdeleRing (𝓞 F) F) (((unipotentGL2 β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) =
    ((unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem W_translate (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (α : F) (g h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (g * h) = whittakerCoefficient F pins ψ (fun y => φ (y * h)) α g := by
  simp only [whittakerCoefficient, mul_assoc]

theorem W_const_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (a : ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun y => a * φ y) α g = a * whittakerCoefficient F pins ψ φ α g := by
  simp only [whittakerCoefficient, mul_assoc]
  exact MeasureTheory.integral_const_mul _ _

theorem W_mul_right_of_forall (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : AdelicGL2 (𝓞 F) F) (c : ℂ) (hk : ∀ y, φ (y * k) = c * φ y)
    (α : F) (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (h * k) = c * whittakerCoefficient F pins ψ φ α h := by
  rw [W_translate, show (fun y => φ (y * k)) = fun y => c * φ y from funext hk, W_const_mul]

theorem W_centralScalar_mul (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (z : (AdeleRing (𝓞 F) F)ˣ) (c : ℂ)
    (hz : ∀ y, φ (centralScalar (𝓞 F) F z * y) = c * φ y) (α : F) (h : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (centralScalar (𝓞 F) F z * h) = c * whittakerCoefficient F pins ψ φ α h := by
  rw [← mul_centralScalar_comm]
  exact W_mul_right_of_forall pins ψ φ _ c (fun y => by rw [mul_centralScalar_comm, hz]) α h

end Glue

section IsoFacts

variable {ξ : (productionPinsGeneral ℚ).Z →* ℂˣ} {N : Ideal (𝓞 ℚ)} {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
  {Φ : HeckeEigensystem ℚ ℂ} {θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

def xiVal (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℂ :=
  ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)

theorem Iso.lsxi (h : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ θ) :
    IsLsXiFunction (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).Z ξ θ := by
  letI := (productionPinsGeneral ℚ).mS
  exact ((lsXiMemberAt_iff (𝓞 ℚ) ℚ (productionPinsGeneral ℚ).μ (productionPinsGeneral ℚ).Z ξ
    (productionPinsGeneral ℚ).D θ).mp h.smoothCusp.1.1).1

theorem Iso.left (h : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ θ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    θ (globalPoints (𝓞 ℚ) ℚ γ * g) = θ g :=
  (Iso.lsxi h).left_invariant γ g

theorem Iso.central (h : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ θ)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    θ (centralScalar (𝓞 ℚ) ℚ z * g) = xiVal ξ z * θ g :=
  (Iso.lsxi h).central_transform ⟨z, Subgroup.mem_top z⟩ g

theorem Iso.periodic (h : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ θ)
    (β : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    θ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β + u) * g) = θ (unipotentGL2 u * g) := by
  rw [unipotentGL2_add, ← globalPoints_unipotentGL2, mul_assoc, Iso.left h]

theorem Iso.level (h : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ θ)
    (g u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) :
    θ (g * u) = θ g :=
  h.level_invariant g u hu

theorem Iso.cuspW (h : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ θ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsOf ℚ D0 U0 gen0 (adelicBox ℚ)) NumberField.StandardAddChar.psiQ θ 0 g = 0 :=
  (whittakerCoefficient_zero_eq_constantTerm ℚ _ _ θ g).trans (h.smoothCusp.1.2 g)

theorem Iso.unipotentInt_inv (h : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ θ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (u : v.adicCompletionIntegers ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    θ (x * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v (unipotentInt (v.adicCompletion ℚ) u))) = θ x :=
  Iso.level h x _ (finEmbed_localEmbed_unipotentInt_mem v N u)

end IsoFacts

section PsiFacts

open NumberField.StandardAddChar

theorem psiQ_adeleSingleAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    psiQ (adeleSingleAt ℚ v x) = psiV v x := by
  rw [adeleSingleAt_apply]; erw [psiQ_apply]
  rw [show (((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ v x) : AdeleRing (𝓞 ℚ) ℚ).1 = 0 from rfl,
    show (((0 : InfiniteAdeleRing ℚ), finAdeleSingleAt ℚ v x) : AdeleRing (𝓞 ℚ) ℚ).2 = finAdeleSingleAt ℚ v x from rfl,
    AddChar.map_zero_eq_one, one_mul, psiFin_apply]
  classical
  rw [finprod_eq_single (fun w => psiV w ((finAdeleSingleAt ℚ v x) w)) v (fun w hw => by
    show psiV w ((finAdeleSingleAt ℚ v x) w) = 1
    rw [finAdeleSingleAt_apply_of_ne ℚ v x hw]; exact AddChar.map_zero_eq_one _)]
  show psiV v ((finAdeleSingleAt ℚ v x) v) = _
  rw [finAdeleSingleAt_apply_self]

theorem psiQ_level_zero (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ)
    (hx : Valued.v x ≤ WithZero.exp (0 : ℤ)) : psiQ (adeleSingleAt ℚ v x) = 1 := by
  rw [psiQ_adeleSingleAt]
  refine psiV_eq_one_of_mem_integers v ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero]
  exact hx

theorem psiQ_level_sharp (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ psiQ (adeleSingleAt ℚ v x) ≠ 1 := by
  refine ⟨algebraMap ℚ (v.adicCompletion ℚ) ((natGenerator v : ℚ))⁻¹, ?_, ?_⟩
  · rw [map_inv₀, map_inv₀, RatIdele.valued_algebraMap_rat, RatIdele.valuation_natGenerator, ← WithZero.exp_neg, neg_neg]
  · rw [psiQ_adeleSingleAt]
    exact psiV_algebraMap_inv_ne_one v

end PsiFacts

section RatArch

theorem glArch_ext_rat {k k' : GL (Fin 2) (InfiniteAdeleRing ℚ)}
    (h : archComponent ℚ Rat.infinitePlace k = archComponent ℚ Rat.infinitePlace k') : k = k' := by
  apply Units.ext
  ext i j
  funext w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  have := congrArg (fun m : GL (Fin 2) Rat.infinitePlace.Completion =>
    (m : Matrix (Fin 2) (Fin 2) Rat.infinitePlace.Completion) i j) h
  simpa only [archComponent_apply] using this

def realGL (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw₀).toRingHom
    (archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g))

theorem glEquiv_symm_realGL (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw₀).symm (realGL g) =
      archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g) := by
  apply Units.ext
  ext i j
  show (ringEquivRealOfIsReal hw₀).symm ((ringEquivRealOfIsReal hw₀).toRingHom
    ((archComponent ℚ Rat.infinitePlace (glArch (𝓞 ℚ) ℚ g) : Matrix (Fin 2) (Fin 2) _) i j)) = _
  exact (ringEquivRealOfIsReal hw₀).symm_apply_apply _

theorem archRealGLAt_realGL_eq (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealGLAt hw₀ (realGL g) = adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ g) := by
  apply eq_of_parts_eq
  · rw [glArch_adelicArchGLIncl]
    unfold archRealGLAt adelicArchGLInclAt
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
      glEquiv_symm_realGL]
    apply glArch_ext_rat
    rw [archComponent_archGLIncl_self]
  · rw [glFin_adelicArchGLIncl]
    unfold archRealGLAt adelicArchGLInclAt
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

theorem eq_archRealGLAt_realGL_of_glFin_eq_one (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : glFin (𝓞 ℚ) ℚ g = 1) :
    g = archRealGLAt hw₀ (realGL g) := by
  rw [archRealGLAt_realGL_eq]
  conv_lhs => rw [eq_archPart_mul_finPart g]
  rw [hg, map_one, mul_one]

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (archRealGLAt hw₀ m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem glArch_archRealGLAt_ne : glArch (𝓞 ℚ) ℚ (archRealGLAt hw₀ (1 : GL (Fin 2) ℝ)) = 1 := by
  rw [map_one, map_one]

theorem archRealLiftAt_coe (m : GL (Fin 2) ℝ) :
    archRealLiftAt hw₀ (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ)) = archRealGLAt hw₀ m := by
  have hdet : (Matrix.of (Matrix.of.symm (m : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply]; exact Matrix.GeneralLinearGroup.det_ne_zero m
  rw [archRealLiftAt_of_det_ne_zero hw₀ hdet]
  congr 1
  apply Units.ext
  simp only [Equiv.apply_symm_apply]
  rfl

end RatArch

section G0

theorem exists_g0 {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), θ (globalPoints (𝓞 ℚ) ℚ γ * g) = θ g)
    (hlev : ∀ (g u : AdelicGL2 (𝓞 ℚ) ℚ), u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ → θ (g * u) = θ g)
    (hne : θ ≠ 0) :
    ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g₀ = 1 ∧ θ g₀ ≠ 0 := by
  obtain ⟨g, hg⟩ : ∃ g, θ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨γ, hk, -⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g
  set k := globalPoints (𝓞 ℚ) ℚ γ * g with hkdef
  refine ⟨adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ k), glFin_adelicArchGLIncl ℚ _, ?_⟩
  have hf : finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ k) ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ :=
    ⟨(finEmbed_mem_levelOne_iff (𝓞 ℚ) ℚ _).mpr ((mem_levelOne_iff).mp hk), finEmbed_mem_finiteAdelicGL2Subgroup _⟩
  rw [← hlev _ _ hf, ← eq_archPart_mul_finPart k, hkdef, hleft]
  exact hg

end G0

section Idele

variable {F : Type} [Field F] [NumberField F]

theorem valued_finIdele_ne_zero (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  intro h
  have : ((δ * δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := by
    rw [mul_inv_cancel, Units.val_one, coe_one_apply]
  rw [Units.val_mul, coe_mul_apply, h, zero_mul] at this
  exact zero_ne_one this

theorem valued_inv_finIdele (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
  rw [← map_mul, ← coe_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, coe_one_apply, map_one]

theorem finite_setOf_valued_ne_one (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) ≠ 1}.Finite := by
  have hδ : ∀ᶠ v in Filter.cofinite, (δ : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    (δ : FiniteAdeleRing (𝓞 F) F).2
  have hδi : ∀ᶠ v in Filter.cofinite, ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F).2
  refine Set.Finite.subset (Filter.eventually_cofinite.mp (hδ.and hδi)) ?_
  intro v hv hgood
  apply hv
  exact le_antisymm hgood.1 (le_of_eq_of_le (valued_inv_finIdele δ v).symm (mul_le_of_le_one_right' hgood.2))

theorem heckeGenAt_mem_of_valued_eq_one (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) (N : Ideal (𝓞 F)) :
    heckeGenAt (𝓞 F) F v u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine ⟨?_, ?_⟩
  · have := heckeGenAt_inv_mul_heckeGenAt_mem_levelOne (R := 𝓞 F) (K := F) (v := v) 1 u
      (by rw [Units.val_one, map_one, hu]) N
    rwa [map_one, inv_one, one_mul] at this
  · exact (mem_finiteAdelicGL2Subgroup_iff F _).mpr (glArch_finIdeleDiag F (localUnit (𝓞 F) F v u))

theorem finIdeleDiag_mem_of_forall_valued_eq_one (δ : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (h : ∀ v, Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v) = 1) (N : Ideal (𝓞 F)) :
    finIdeleDiag F δ ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  have hi : ∀ (ε : (FiniteAdeleRing (𝓞 F) F)ˣ), (∀ v, Valued.v ((ε : FiniteAdeleRing (𝓞 F) F) v) = 1) →
      IsLevelOneMatrix (𝓞 F) F N
        (glFin (𝓞 F) F (finIdeleDiag F ε) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
    intro ε hε
    have hint : (ε : FiniteAdeleRing (𝓞 F) F) ∈ AdelicLevel.integralFiniteAdeles (𝓞 F) F := fun v => by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hε v]
    refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
    · fin_cases i <;> fin_cases j
      · exact hint
      · exact zero_mem_integralFiniteAdeles
      · exact zero_mem_integralFiniteAdeles
      · exact one_mem_integralFiniteAdeles
    · exact zero_mem_idealBall N
    · show (1 : FiniteAdeleRing (𝓞 F) F) - 1 ∈ idealBall (𝓞 F) F N
      rw [sub_self]; exact zero_mem_idealBall N
  have hinv : ∀ v, Valued.v (((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 :=
    fun v => by have := valued_inv_finIdele δ v; rwa [h v, one_mul] at this
  refine ⟨?_, (mem_finiteAdelicGL2Subgroup_iff F _).mpr (glArch_finIdeleDiag F δ)⟩
  refine ⟨hi δ h, ?_⟩
  rw [← map_inv, ← map_inv]
  exact hi δ⁻¹ hinv

theorem finComponent_glFin_finIdeleDiag_eq_one (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F))
    (hv : (δ : FiniteAdeleRing (𝓞 F) F) v = 1) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (finIdeleDiag F δ)) = 1 := by
  ext i j
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j
  · exact hv
  · rfl
  · rfl
  · rfl

theorem finIdele_split_at (δ : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (δ' : (FiniteAdeleRing (𝓞 F) F)ˣ) (u : (v.adicCompletion F)ˣ) (e : ℤ),
      (δ' : FiniteAdeleRing (𝓞 F) F) v = 1 ∧
      (∀ w, w ≠ v → (δ' : FiniteAdeleRing (𝓞 F) F) w = (δ : FiniteAdeleRing (𝓞 F) F) w) ∧
      Valued.v (u : v.adicCompletion F) = 1 ∧
      δ = δ' * (localUnit (𝓞 F) F v u * localUnit (𝓞 F) F v (uniformizerUnit F v) ^ e) := by
  classical
  have hne : (δ : FiniteAdeleRing (𝓞 F) F) v ≠ 0 := (Valuation.ne_zero_iff _).mp (valued_finIdele_ne_zero δ v)
  set t : (v.adicCompletion F)ˣ := Units.mk0 ((δ : FiniteAdeleRing (𝓞 F) F) v) hne with ht
  set e : ℤ := - WithZero.log (Valued.v ((δ : FiniteAdeleRing (𝓞 F) F) v)) with he
  refine ⟨δ * (localUnit (𝓞 F) F v t)⁻¹, t * (uniformizerUnit F v) ^ (-e), e, ?_, ?_, ?_, ?_⟩
  · rw [← map_inv, Units.val_mul, coe_mul_apply, localUnit_apply_self, Units.val_inv_eq_inv_val, ht,
      Units.val_mk0, mul_inv_cancel₀ hne]
  · intro w hw
    rw [← map_inv, Units.val_mul, coe_mul_apply, localUnit_apply_of_ne (𝓞 F) F v _ hw, mul_one]
  · have hvt : Valued.v (t : v.adicCompletion F) = WithZero.exp (-e) := by
      rw [ht, Units.val_mk0, he, neg_neg, WithZero.exp_log (valued_finIdele_ne_zero δ v)]
    rw [Units.val_mul, map_mul, hvt, Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg, ← WithZero.exp_add, add_neg_cancel,
      WithZero.exp_zero]
  · rw [map_mul, map_zpow, _root_.zpow_neg]
    group

end Idele

def IsComb (φ θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
    (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ θ = fun x => ∑ i, c i * φ (x * g i)

theorem isComb_self (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : IsComb φ φ :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, by funext x; simp⟩

theorem IsComb.cosetSum {φ θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (h : IsComb φ θ) {k : ℕ}
    (r : Fin k → AdelicGL2 (𝓞 ℚ) ℚ) (hr : ∀ j, r j ∈ finiteAdelicGL2Subgroup ℚ) :
    IsComb φ (fun x => ∑ j, θ (x * r j)) := by
  obtain ⟨m, c, g, hg, rfl⟩ := h
  refine ⟨k * m, fun q => c (finProdFinEquiv.symm q).2,
    fun q => r (finProdFinEquiv.symm q).1 * g (finProdFinEquiv.symm q).2,
    fun q => mul_mem (hr _) (hg _), ?_⟩
  funext x
  simp only [mul_assoc]
  rw [← Fintype.sum_prod_type' (fun j i => c i * φ (x * (r j * g i)))]
  exact Fintype.sum_equiv finProdFinEquiv _ _ (fun q => by simp only [Equiv.symm_apply_apply])

section Strip

variable (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (Φ : HeckeEigensystem ℚ ℂ)

theorem hPI : IsPrincipalInvariantAddChar ℚ NumberField.StandardAddChar.psiQ :=
  NumberField.StandardAddChar.isGlobalAddChar_psiQ.principalInvariant

theorem W1_cosetSum {m : ℕ} (r : Fin m → AdelicGL2 (𝓞 ℚ) ℚ) (θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hθ : Continuous θ)
    (h : AdelicGL2 (𝓞 ℚ) ℚ) :
    W1 (fun x => ∑ i, θ (x * r i)) 1 h = ∑ i, W1 θ 1 (h * r i) := by
  have key := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous ℚ D0 U0 gen0 NumberField.StandardAddChar.psiQ
    NumberField.StandardAddChar.continuous_psiQ m (fun j => fun x => θ (x * r j))
    (fun j => hθ.comp (continuous_mul_const (r j))) (fun _ => 1) 1 h
  simp only [one_mul] at key
  rw [key]
  exact Finset.sum_congr rfl fun i _ => (W_translate _ _ θ 1 h (r i)).symm

theorem W1_inv_eq_zero {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} {θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S' Φ θ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) = 1)
    (k : ℕ) : W1 θ 1 (g * (heckeGen (𝓞 ℚ) ℚ p ^ (k + 1))⁻¹) = 0 :=
  AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_inv_eq_zero ℚ D0 U0 gen0 NumberField.StandardAddChar.psiQ hPI p
    (psiQ_level_sharp p) θ (Iso.periodic hiso) (Iso.unipotentInt_inv hiso p) g hg k

theorem exists_heckeOp (hN : N ≠ ⊥) (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (m : ℕ) (loc : Fin m → GL (Fin 2) (p.adicCompletion ℚ)) (cQ d : ℂ), cQ ≠ 0 ∧
      HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (heckeGen (𝓞 ℚ) ℚ p)
        (fun i => finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p (loc i))) ∧
      ∀ (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
        IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S' Φ θ →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) = 1 → ∀ n : ℕ,
          W1 (fun x => ∑ i, θ (x * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p (loc i)))) 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ n)
            = cQ * W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ (n + 1))
              + d * W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ n * (heckeGen (𝓞 ℚ) ℚ p ^ 1)⁻¹) := by
  classical
  have habs : Ideal.absNorm p.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero p.ne_bot)
  haveI hfinQ : Finite (𝓞 ℚ ⧸ p.asIdeal) := (Ideal.absNorm_ne_zero_iff p.asIdeal).mp habs
  letI : Fintype (𝓞 ℚ ⧸ p.asIdeal) := Fintype.ofFinite _
  have hcQ : ((Fintype.card (𝓞 ℚ ⧸ p.asIdeal) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hdvd : p.asIdeal ∣ N
  · obtain ⟨ϖ, hϖ0, hval, hgen, sec, hsec, hsys⟩ :=
      HeckeIntegralSeam.exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd ℚ p N hdvd hN
    refine ⟨Fintype.card (𝓞 ℚ ⧸ p.asIdeal),
      fun i => localRepSome ϖ hϖ0 (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ)
        (sec ((Fintype.equivFin (𝓞 ℚ ⧸ p.asIdeal)).symm i))),
      (Fintype.card (𝓞 ℚ ⧸ p.asIdeal) : ℂ), 0, hcQ,
      isHeckeCosetSystem_comp_equiv (Fintype.equivFin (𝓞 ℚ ⧸ p.asIdeal)).symm hsys, ?_⟩
    intro S' θ hiso g hg n
    rw [W1_cosetSum _ θ hiso.continuous, zero_mul, add_zero]
    rw [Finset.sum_congr rfl fun i _ =>
      AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq ℚ D0 U0 gen0
        NumberField.StandardAddChar.psiQ hPI p (psiQ_level_zero p) ϖ hϖ0 hgen θ (Iso.periodic hiso) g hg n _]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · obtain ⟨ϖ, hϖ0, hval, hgen, sec, hsec, hsysAll⟩ :=
      HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen ℚ p
    have hsys := hsysAll N hdvd
    set e : Fin (Fintype.card (Option (𝓞 ℚ ⧸ p.asIdeal))) ≃ Option (𝓞 ℚ ⧸ p.asIdeal) :=
      (Fintype.equivFin (Option (𝓞 ℚ ⧸ p.asIdeal))).symm with he
    refine ⟨Fintype.card (Option (𝓞 ℚ ⧸ p.asIdeal)),
      fun i => (e i).elim (localRepInf ϖ hϖ0)
        (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (sec c))),
      (Fintype.card (𝓞 ℚ ⧸ p.asIdeal) : ℂ),
      xiVal ξ (Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ)
        (localUnit (𝓞 ℚ) ℚ p (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hϖ0))),
      hcQ, isHeckeCosetSystem_comp_equiv e hsys, ?_⟩
    intro S' θ hiso g hg n
    rw [W1_cosetSum _ θ hiso.continuous]
    rw [Fintype.sum_equiv e
      (fun i => W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ n * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p ((e i).elim (localRepInf ϖ hϖ0)
        (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (sec c)))))))
      (fun o => W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ n * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p (o.elim (localRepInf ϖ hϖ0)
        (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 ℚ) (p.adicCompletionIntegers ℚ) (sec c)))))))
      (fun i => rfl)]
    rw [Fintype.sum_option]
    have h2 := AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq ℚ
      (productionPinsOf ℚ D0 U0 gen0 (adelicBox ℚ)) NumberField.StandardAddChar.psiQ p ϖ hϖ0 hgen θ (xiVal ξ)
      (Iso.central hiso) (g * heckeGen (𝓞 ℚ) ℚ p ^ n * (heckeGen (𝓞 ℚ) ℚ p ^ 1)⁻¹) 0
    rw [zero_add, pow_zero, mul_one, inv_mul_cancel_right] at h2
    simp only [Option.elim_none, Option.elim_some]
    rw [h2, Finset.sum_congr rfl fun c _ =>
      AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_mul_localRepSome_eq ℚ D0 U0 gen0
        NumberField.StandardAddChar.psiQ hPI p (psiQ_level_zero p) ϖ hϖ0 hgen θ (Iso.periodic hiso) g hg n _]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_comm]

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)

theorem strip_prime_aux (hN : N ≠ ⊥) (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hg : finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) = 1) :
    ∀ (n : ℕ) (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), S ⊆ S' →
      IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S' Φ θ → IsComb φ θ →
      (∀ m : ℕ, m < n → W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ m) = 0) → W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ n) ≠ 0 →
      ∃ (S'' : Finset (HeightOneSpectrum (𝓞 ℚ))) (θ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), S ⊆ S'' ∧
        IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S'' Φ θ' ∧ IsComb φ θ' ∧ W1 θ' 1 g ≠ 0 := by
  classical
  obtain ⟨m, loc, cQ, d, hcQ, hsys, hrec⟩ := exists_heckeOp ξ N Φ hN p
  intro n
  induction n with
  | zero =>
    intro S' θ hS hiso hcomb _ hn
    exact ⟨S', θ, hS, hiso, hcomb, by simpa using hn⟩
  | succ n ih =>
    intro S' θ hS hiso hcomb hvan hn
    have hisoT : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N (S' ∪ {p} ∪ (N.finite_factors hN).toFinset) Φ
        (fun x => ∑ i, θ (x * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p (loc i)))) :=
      AutomorphicForm.isIsotypicCuspFormAt_sum_apply_mul_finEmbed_localEmbed_of_isHeckeCosetSystem ξ N hN S' Φ θ hiso p
        m loc (heckeGen (𝓞 ℚ) ℚ p) hsys
    have hcombT : IsComb φ (fun x => ∑ i, θ (x * finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p (loc i)))) :=
      hcomb.cosetSum _ (fun i => finEmbed_mem_finiteAdelicGL2Subgroup _)
    have hsecond : ∀ j : ℕ, j ≤ n →
        W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ j * (heckeGen (𝓞 ℚ) ℚ p ^ 1)⁻¹) = 0 := by
      intro j hj
      cases j with
      | zero =>
        rw [pow_zero, mul_one]
        exact W1_inv_eq_zero ξ N Φ hiso p g hg 0
      | succ j' =>
        rw [pow_one, pow_succ, ← mul_assoc, mul_inv_cancel_right]
        exact hvan j' (by omega)
    refine ih (S' ∪ {p} ∪ (N.finite_factors hN).toFinset) _
      (hS.trans (Finset.subset_union_left.trans Finset.subset_union_left)) hisoT hcombT ?_ ?_
    · intro j hj
      rw [hrec S' θ hiso g hg j, hvan (j + 1) (by omega), hsecond j hj.le, mul_zero, mul_zero, add_zero]
    · rw [hrec S' θ hiso g hg n, hsecond n le_rfl, mul_zero, add_zero]
      exact mul_ne_zero hcQ hn

theorem strip_prime (hN : N ≠ ⊥) (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hg : finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ g) = 1)
    {S' : Finset (HeightOneSpectrum (𝓞 ℚ))} {θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hS : S ⊆ S')
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S' Φ θ) (hcomb : IsComb φ θ)
    (e : ℤ) (h : W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ e) ≠ 0) :
    ∃ (S'' : Finset (HeightOneSpectrum (𝓞 ℚ))) (θ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), S ⊆ S'' ∧
      IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S'' Φ θ' ∧ IsComb φ θ' ∧ W1 θ' 1 g ≠ 0 := by
  classical
  have hex : ∃ n : ℕ, W1 θ 1 (g * heckeGen (𝓞 ℚ) ℚ p ^ n) ≠ 0 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
    · exact ⟨n, by rwa [zpow_natCast] at h⟩
    · cases n with
      | zero => exact ⟨0, by simpa using h⟩
      | succ k =>
        exfalso
        apply h
        rw [_root_.zpow_neg, zpow_natCast]
        exact W1_inv_eq_zero ξ N Φ hiso p g hg k
  exact strip_prime_aux ξ N Φ S φ hN p g hg (Nat.find hex) S' θ hS hiso hcomb
    (fun m hm => not_not.mp (Nat.find_min hex hm)) (Nat.find_spec hex)

theorem strip_all (hN : N ≠ ⊥) : ∀ (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (δ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
    (∀ v, v ∉ T → Valued.v ((δ : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) →
    ∀ (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (θ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), S ⊆ S' →
      IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S' Φ θ → IsComb φ θ →
      ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 → W1 θ 1 (x * finIdeleDiag ℚ δ) ≠ 0 →
      ∃ (S'' : Finset (HeightOneSpectrum (𝓞 ℚ))) (θ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ), S ⊆ S'' ∧
        IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S'' Φ θ' ∧ IsComb φ θ' ∧ W1 θ' 1 x ≠ 0 := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro δ hδ S' θ hS hiso hcomb x hx h
    refine ⟨S', θ, hS, hiso, hcomb, ?_⟩
    have hmem := finIdeleDiag_mem_of_forall_valued_eq_one δ (fun v => hδ v (by simp)) N
    rwa [W_mul_right_of_forall _ _ θ _ 1 (fun y => by rw [one_mul]; exact Iso.level hiso y _ hmem), one_mul] at h
  | insert p T hpT ih =>
    intro δ hδ S' θ hS hiso hcomb x hx h
    obtain ⟨δ', u, e, hδ'v, hδ'w, hu, hsplit⟩ := finIdele_split_at δ p
    have hk : heckeGenAt (𝓞 ℚ) ℚ p u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ :=
      heckeGenAt_mem_of_valued_eq_one p u hu N
    have hg : finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (x * finIdeleDiag ℚ δ')) = 1 := by
      rw [map_mul, map_mul, hx, map_one, one_mul, finComponent_glFin_finIdeleDiag_eq_one δ' p hδ'v]
    have hrew : x * finIdeleDiag ℚ δ = x * finIdeleDiag ℚ δ' * heckeGen (𝓞 ℚ) ℚ p ^ e * heckeGenAt (𝓞 ℚ) ℚ p u := by
      rw [hsplit, map_mul, map_mul, map_zpow]
      simp only [mul_assoc]
      congr 2
      show heckeGenAt (𝓞 ℚ) ℚ p u * heckeGenAt (𝓞 ℚ) ℚ p (uniformizerUnit ℚ p) ^ e
        = heckeGenAt (𝓞 ℚ) ℚ p (uniformizerUnit ℚ p) ^ e * heckeGenAt (𝓞 ℚ) ℚ p u
      rw [← map_zpow, ← map_mul, ← map_mul, mul_comm]
    rw [hrew, W_mul_right_of_forall _ _ θ _ 1 (fun y => by rw [one_mul]; exact Iso.level hiso y _ hk), one_mul] at h
    obtain ⟨S₁, θ₁, hS₁, hiso₁, hcomb₁, h₁⟩ := strip_prime ξ N Φ S φ hN p _ hg hS hiso hcomb e h
    refine ih δ' ?_ S₁ θ₁ hS₁ hiso₁ hcomb₁ x hx h₁
    intro v hv
    by_cases hvp : v = p
    · subst hvp; rw [hδ'v, map_one]
    · rw [hδ'w v hvp]
      exact hδ v (fun hmem => (Finset.mem_insert.mp hmem).elim hvp hv)

end Strip

section IdeleSplit

def archIdele (γ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ where
  val := ((γ : AdeleRing (𝓞 ℚ) ℚ).1, 1)
  inv := (((γ⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1, 1)
  val_inv := Prod.ext (show ((γ : AdeleRing (𝓞 ℚ) ℚ) * ((γ⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).1 = (1 : AdeleRing (𝓞 ℚ) ℚ).1 by
    rw [Units.mul_inv]) (mul_one 1)
  inv_val := Prod.ext (show (((γ⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * (γ : AdeleRing (𝓞 ℚ) ℚ)).1 = (1 : AdeleRing (𝓞 ℚ) ℚ).1 by
    rw [Units.inv_mul]) (mul_one 1)

def finIdele (γ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ where
  val := ((γ : AdeleRing (𝓞 ℚ) ℚ)).2
  inv := (((γ⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).2
  val_inv := show ((γ : AdeleRing (𝓞 ℚ) ℚ) * ((γ⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)).2 = (1 : AdeleRing (𝓞 ℚ) ℚ).2 by
    rw [Units.mul_inv]
  inv_val := show (((γ⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) * (γ : AdeleRing (𝓞 ℚ) ℚ)).2 = (1 : AdeleRing (𝓞 ℚ) ℚ).2 by
    rw [Units.inv_mul]

theorem idele_split (γ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    γ = archIdele γ * Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) (finIdele γ) :=
  Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)

theorem glFin_diagOne_archIdele (γ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    glFin (𝓞 ℚ) ℚ (diagOne (archIdele γ)) = 1 := by
  ext i j
  rw [glFin_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem diagOne_map_finIncl (δ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    diagOne (Units.map (finIncl (𝓞 ℚ) ℚ : FiniteAdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 ℚ) ℚ) δ) = finIdeleDiag ℚ δ := rfl

theorem mul_comm_of_glFin_of_glArch (a b : AdelicGL2 (𝓞 ℚ) ℚ) (ha : glFin (𝓞 ℚ) ℚ a = 1) (hb : glArch (𝓞 ℚ) ℚ b = 1) :
    a * b = b * a := by
  refine eq_of_parts_eq ?_ ?_
  · rw [map_mul, map_mul, hb, mul_one, one_mul]
  · rw [map_mul, map_mul, ha, mul_one, one_mul]

end IdeleSplit

end P2M.Strip100

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AdelicDock LocalGL2 P2M.Strip100 in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (hne : φ ≠ 0)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ) :
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      S ⊆ S' ∧
      φ' ∈ V ∧
      IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S' Φ φ' ∧
      φ' ≠ 0 ∧
      (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ' α = φ') ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (n : ℤ),
        HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ → HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ') ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ),
        (IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
          (IsArchSmoothAt hw φ' ∧ archCasimirAt hw φ' = lam • φ')) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (e : ℂ),
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = e * φ g) →
          ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ' (g * archRealGLAt hw UpperHalfPlane.J) = e * φ' g) ∧

      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (cJ : ℂ),
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J)
            = cJ * (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) g) →
          ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ' (g * archRealGLAt hw UpperHalfPlane.J)
            = cJ * (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) g) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        archDerivAt hw ArchDir.H φ
            - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0 →
          archDerivAt hw ArchDir.H φ'
            - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ') = 0) ∧
      ∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' 1 (diagOne a) ≠ 0 := by
  classical

  obtain ⟨tys, htys⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent ξ V hV φ hφV
  have hcut : φ ∈ V ⊓ levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓ archCutSubmodule ℚ tys :=
    ⟨⟨hφV, hiso.level_invariant⟩, htys⟩
  have hX : V ⊓ levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓ archCutSubmodule ℚ tys ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨φ, hcut, hne⟩
  have hsmV : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∀ x ∈ V, IsArchSmoothAt hw x := by
    intro w hw x hx
    obtain ⟨lam, h⟩ :=
      AutomorphicForm.CuspidalConstituent.exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isCuspConstituent ℚ
        (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov_std ξ V hV N hN tys hX w hw
    exact (h x hx).1

  obtain ⟨g₀, hg₀fin, hg₀⟩ := exists_g0 hN φ (Iso.left hiso) (Iso.level hiso) hne

  have harch := AutomorphicForm.contDiff_apply_unipotentGL2_mixedSpace_mul_of_isArchSmoothAt_rat φ (hsmV _ hw₀ φ hφV)
  obtain ⟨γ, -, hWγ⟩ :=
    AutomorphicForm.exists_mem_principalIdeles_whittakerCoefficient_one_diagOne_mul_ne_zero ℚ D0 U0 gen0
      NumberField.StandardAddChar.psiQ NumberField.StandardAddChar.isGlobalAddChar_psiQ φ hiso.continuous (Iso.left hiso)
      hiso.smoothCusp.2 harch (Iso.cuspW hiso) g₀ hg₀

  set x : AdelicGL2 (𝓞 ℚ) ℚ := diagOne (archIdele γ) * g₀ with hxdef
  have hx : glFin (𝓞 ℚ) ℚ x = 1 := by rw [hxdef, map_mul, glFin_diagOne_archIdele, hg₀fin, mul_one]
  have hpt : diagOne γ * g₀ = x * finIdeleDiag ℚ (finIdele γ) := by
    rw [idele_split γ, map_mul, diagOne_map_finIncl, hxdef, mul_assoc, mul_assoc,
      mul_comm_of_glFin_of_glArch g₀ _ hg₀fin (glArch_finIdeleDiag ℚ _), ← idele_split γ]
  rw [hpt] at hWγ

  obtain ⟨S', φ', hS', hiso', hcomb', hW'⟩ :=
    strip_all ξ N Φ S φ hN (finite_setOf_valued_ne_one (finIdele γ)).toFinset (finIdele γ)
      (fun v hv => by simpa [Set.Finite.mem_toFinset] using hv) S φ (Finset.Subset.refl S) hiso (isComb_self φ) x hx hWγ

  obtain ⟨m, c, g, hg, hφ'eq⟩ := hcomb'
  obtain ⟨hV', -, hcut', hwt', hcas', hrefl', hJ', hlow'⟩ :=
    AutomorphicForm.CuspidalConstituent.sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
      ξ V hV hsmV φ hφV m c g hg
  rw [← hφ'eq] at hV' hcut' hwt' hcas' hrefl' hJ' hlow'

  obtain ⟨n₀, hn₀⟩ := hwt w₀ hw₀
  obtain ⟨a, ha, hWa⟩ :=
    AutomorphicForm.exists_whittakerCoefficient_one_diagOne_ne_zero_of_glFin_eq_one_rat D0 U0 gen0 φ' (Iso.periodic hiso')
      (xiVal ξ) (Iso.central hiso') n₀ (hwt' w₀ hw₀ n₀ hn₀) x hx hW'

  have hrep := AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
    ξ V hV N hN tys φ' ⟨⟨hV', hiso'.level_invariant⟩, hcut' tys htys⟩

  have hne' : φ' ≠ 0 := by
    rintro rfl
    exact hWa (AutomorphicForm.whittakerCoefficient_zero ℚ _ _ 1 _)
  exact ⟨S', φ', hS', hV', hiso', hne', hrep, hwt', hcas', hrefl', hJ', hlow', a, ha, hWa⟩

end

end S_LanglandsTunnell_exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt
end P2MW
export P2MW.S_LanglandsTunnell_exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt (solution)
