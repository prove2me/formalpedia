-- Prove2me | solution 1 for NumberField.TateGlobal.exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4324e292-a089-551a-abc3-36ceee7a88ce

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_LanglandsTunnell_ArchPlace
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum
import Theorems.Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_HeckeTate_finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Mathlib
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk"
p2m_attr_erase "simp" "TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.ArchPlace NumberField.StandardAddChar LanglandsTunnell.TateLocal

open scoped Classical

namespace F1Z

section ArchPinsAux

p2m_open "NumberField.InfinitePlace.Completion Complex"

variable {K : Type} [Field K] [NumberField K]

theorem norm_ext_aux (w : InfinitePlace K) (x : w.Completion) : ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem ideleNorm_archUnitHom_aux (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  have h1 : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)).erase w,
      ‖((archUnitHom w x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = 1 := by
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) v‖ ^ v.mult = 1
    rw [Function.update_of_ne hvw]
    change ‖(1 : v.Completion)‖ ^ v.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one h1, one_mul]
  show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) w‖ ^ w.mult = _
  rw [Function.update_self]

theorem coe_realCharFun_aux (u : ℂ) (a : ZMod 2) (y : ℝˣ) :
    ((realCharFun u a y : ℂˣ) : ℂ) = ((‖(y : ℝ)‖ : ℂ) ^ u) * ((((y : ℝ) : ℂ) / (‖(y : ℝ)‖ : ℂ))) ^ (a.val : ℕ) := by
  show ((Units.mk0 ((‖(y : ℝ)‖ : ℂ) ^ u) _ * realSign y ^ (a.val : ℕ) : ℂˣ) : ℂ) = _
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  rfl

theorem sign_zpow_eq_pow_val (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (m : ℤ) : σ ^ m = σ ^ (((m : ℤ) : ZMod 2).val : ℕ) := by
  rcases hσ with rfl | rfl
  · simp
  · rcases Int.even_or_odd m with hm | hm
    · rw [hm.neg_one_zpow, (ZMod.intCast_zmod_eq_zero_iff_dvd m 2).mpr (even_iff_two_dvd.mp hm), ZMod.val_zero, pow_zero]
    · rw [hm.neg_one_zpow]
      have : ((m : ℤ) : ZMod 2) = 1 := by
        obtain ⟨j, hj⟩ := hm; rw [hj]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
      rw [this, ZMod.val_one, pow_one]

end ArchPinsAux

section ArchPins

p2m_open "NumberField.InfinitePlace.Completion Complex"

variable (K : Type) [Field K] [NumberField K]

theorem archPins_real (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
    (i : {w : InfinitePlace K // w.IsReal}) (x : (i.1.Completion)ˣ) :
    χ (archUnitHom i.1 x) =
      realCharFun (((τ i.1 : ℝ) : ℂ) * Complex.I) (((m i.1 : ℤ) : ZMod 2))
        (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2).toMonoidHom x) := by
  obtain ⟨w, hw⟩ := i
  have hmult : w.mult = 1 := by simp [InfinitePlace.mult, hw]
  set eR := extensionEmbeddingOfIsReal hw with heR
  set r : ℝ := eR (x : w.Completion) with hr
  have hr0 : r ≠ 0 := by
    intro h0
    exact x.ne_zero ((map_eq_zero eR).mp h0)
  have habs : 0 < |r| := abs_pos.mpr hr0

  obtain ⟨y₁, hy₁⟩ := (bijective_extensionEmbeddingOfIsReal hw).2 (|r|)
  obtain ⟨y₂, hy₂⟩ := (bijective_extensionEmbeddingOfIsReal hw).2 (r / |r|)
  have hy₁0 : y₁ ≠ 0 := by intro h0; rw [h0, map_zero] at hy₁; exact habs.ne' hy₁.symm
  have hsg0 : r / |r| ≠ 0 := div_ne_zero hr0 habs.ne'
  have hy₂0 : y₂ ≠ 0 := by intro h0; rw [h0, map_zero] at hy₂; exact hsg0 hy₂.symm
  set x₁ : (w.Completion)ˣ := Units.mk0 y₁ hy₁0 with hx₁
  set x₂ : (w.Completion)ˣ := Units.mk0 y₂ hy₂0 with hx₂
  have hx : x = x₁ * x₂ := by
    apply Units.ext
    apply eR.injective
    show eR (x : w.Completion) = eR (y₁ * y₂)
    rw [map_mul, hy₁, hy₂, ← hr]
    field_simp
  have he₁ : extensionEmbedding w (x₁ : w.Completion) = ((|r| : ℝ) : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hw]; change ((eR y₁ : ℝ) : ℂ) = _; rw [hy₁]
  have he₂ : extensionEmbedding w (x₂ : w.Completion) = ((r / |r| : ℝ) : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hw]; change ((eR y₂ : ℝ) : ℂ) = _; rw [hy₂]
  have hsg1 : ‖((r / |r| : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs, div_self habs.ne']
  have hsg : ((r / |r| : ℝ) : ℂ) = 1 ∨ ((r / |r| : ℝ) : ℂ) = -1 := by
    rcases lt_or_gt_of_ne hr0 with h | h
    · right; rw [abs_of_neg h]; push_cast; rw [div_neg, div_self (by exact_mod_cast hr0)]
    · left; rw [abs_of_pos h, div_self hr0]; push_cast; rfl

  have h1 : ((χ (archUnitHom w x₁) : ℂˣ) : ℂ) = ((|r| : ℝ) : ℂ) ^ (((τ w : ℝ) : ℂ) * Complex.I) := by
    have := hτ w x₁ (by rw [he₁, Complex.ofReal_re]; exact habs) (by rw [he₁, Complex.ofReal_im])
    rw [show archLocalChar χ w x₁ = χ (archUnitHom w x₁) from rfl, ideleNorm_archUnitHom_aux, hmult, pow_one,
      ← norm_ext_aux, he₁, Complex.norm_real, Real.norm_eq_abs, abs_abs] at this
    exact this
  have h2 : ((χ (archUnitHom w x₂) : ℂˣ) : ℂ) = ((r / |r| : ℝ) : ℂ) ^ (m w) := by
    have := hm w x₂ (by rw [he₂]; exact hsg1)
    rw [show archLocalChar χ w x₂ = χ (archUnitHom w x₂) from rfl, he₂] at this
    exact this

  apply Units.ext
  have hxR : ((Units.map eR.toMonoidHom x : ℝˣ) : ℝ) = r := rfl
  rw [hx, map_mul, map_mul, Units.val_mul, h1, h2, coe_realCharFun_aux, ← hx]
  simp only [hxR]
  rw [Real.norm_eq_abs, sign_zpow_eq_pow_val _ hsg (m w)]
  push_cast
  rfl

theorem archPins_complex (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
    (j : {w : InfinitePlace K // w.IsComplex}) (z : (j.1.Completion)ˣ) :
    χ (archUnitHom j.1 z) =
      complexCharFun (((τ j.1 : ℝ) : ℂ) * Complex.I) (m j.1)
        (Units.map (InfinitePlace.Completion.extensionEmbedding j.1).toMonoidHom z) := by
  obtain ⟨w, hw⟩ := j
  have hmult : w.mult = 2 := by
    have : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
    simp [InfinitePlace.mult, this]
  set e := extensionEmbedding w with he
  set c : ℂ := e (z : w.Completion) with hc
  have hc0 : c ≠ 0 := by intro h0; exact z.ne_zero ((map_eq_zero e).mp h0)
  have hnc : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  obtain ⟨y₁, hy₁⟩ := surjective_extensionEmbedding_of_isComplex hw ((‖c‖ : ℝ) : ℂ)
  obtain ⟨y₂, hy₂⟩ := surjective_extensionEmbedding_of_isComplex hw (c / (‖c‖ : ℂ))
  have hph0 : c / (‖c‖ : ℂ) ≠ 0 := div_ne_zero hc0 (by exact_mod_cast hnc.ne')
  have hy₁0 : y₁ ≠ 0 := by intro h0; rw [h0, map_zero] at hy₁; exact (by exact_mod_cast hnc.ne' : ((‖c‖ : ℝ) : ℂ) ≠ 0) hy₁.symm
  have hy₂0 : y₂ ≠ 0 := by intro h0; rw [h0, map_zero] at hy₂; exact hph0 hy₂.symm
  set z₁ : (w.Completion)ˣ := Units.mk0 y₁ hy₁0 with hz₁
  set z₂ : (w.Completion)ˣ := Units.mk0 y₂ hy₂0 with hz₂
  have hz : z = z₁ * z₂ := by
    apply Units.ext
    apply e.injective
    show e (z : w.Completion) = e (y₁ * y₂)
    rw [map_mul]
    change c = extensionEmbedding w y₁ * extensionEmbedding w y₂
    have hnc' : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnc.ne'
    rw [hy₁, hy₂]
    field_simp
  have he₁ : extensionEmbedding w (z₁ : w.Completion) = ((‖c‖ : ℝ) : ℂ) := hy₁
  have he₂ : extensionEmbedding w (z₂ : w.Completion) = c / (‖c‖ : ℂ) := hy₂
  have hph1 : ‖c / (‖c‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnc, div_self hnc.ne']
  have h1 : ((χ (archUnitHom w z₁) : ℂˣ) : ℂ) = (((‖c‖ ^ 2 : ℝ)) : ℂ) ^ (((τ w : ℝ) : ℂ) * Complex.I) := by
    have := hτ w z₁ (by rw [he₁, Complex.ofReal_re]; exact hnc) (by rw [he₁, Complex.ofReal_im])
    rw [show archLocalChar χ w z₁ = χ (archUnitHom w z₁) from rfl, ideleNorm_archUnitHom_aux, hmult,
      ← norm_ext_aux, he₁, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnc] at this
    exact this
  have h2 : ((χ (archUnitHom w z₂) : ℂˣ) : ℂ) = (c / (‖c‖ : ℂ)) ^ (m w) := by
    have := hm w z₂ (by rw [he₂]; exact hph1)
    rw [show archLocalChar χ w z₂ = χ (archUnitHom w z₂) from rfl, he₂] at this
    exact this
  have hsq : (((‖c‖ ^ 2 : ℝ)) : ℂ) ^ (((τ w : ℝ) : ℂ) * Complex.I) = ((‖c‖ : ℝ) : ℂ) ^ (2 * (((τ w : ℝ) : ℂ) * Complex.I)) := by
    have hr0' : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnc.ne'
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hnc 2).ne'), Complex.cpow_def_of_ne_zero hr0',
      ← Complex.ofReal_log (pow_pos hnc 2).le, ← Complex.ofReal_log hnc.le, Real.log_pow]
    congr 1; push_cast; ring
  apply Units.ext
  have hzC : ((Units.map e.toMonoidHom z : ℂˣ) : ℂ) = c := rfl
  rw [hz, map_mul, map_mul, Units.val_mul, h1, h2, complexCharFun_apply, LanglandsTunnell.ArchPlace.anglePhase, ← hz]
  simp only [hzC]
  rw [hsq]

theorem gamma_eq_prod_subtype (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (s : ℂ) :
    (∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)))
      = (∏ i : {w : InfinitePlace K // w.IsReal},
            Complex.Gammaℝ (s + ((((τ i.1 : ℝ) : ℂ) * Complex.I) + signShift (((m i.1 : ℤ) : ZMod 2)))))
        * ∏ j : {w : InfinitePlace K // w.IsComplex},
            Complex.Gammaℂ (s + ((((τ j.1 : ℝ) : ℂ) * Complex.I) + (((m j.1).natAbs : ℕ) : ℂ) / 2)) := by
  have hss : ∀ m : ℤ, signShift ((m : ℤ) : ZMod 2) = (((m.natAbs % 2 : ℕ)) : ℂ) := by
    intro m
    unfold signShift
    rcases Int.even_or_odd m with hm | hm
    · have h0 : ((m : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd m 2).mpr (even_iff_two_dvd.mp hm)
      have h2 : m.natAbs % 2 = 0 := Nat.even_iff.mp (Int.natAbs_even.mpr hm)
      rw [if_pos h0, h2]; simp
    · have h1 : ((m : ℤ) : ZMod 2) ≠ 0 := fun h =>
        (Int.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd m 2).mp h))
      have h2 : m.natAbs % 2 = 1 := Nat.odd_iff.mp (Int.natAbs_odd.mpr hm)
      rw [if_neg h1, h2]; simp
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => w.IsReal)]
  congr 1
  · refine Fintype.prod_congr _ _ fun i => ?_
    rw [if_pos i.2, hss, add_assoc]
  · calc ∏ v : {w : InfinitePlace K // ¬ w.IsReal},
          (if v.1.IsReal then Complex.Gammaℝ (s + ((τ v.1 : ℝ) : ℂ) * Complex.I + (((m v.1).natAbs % 2 : ℕ) : ℂ))
            else Complex.Gammaℂ (s + ((τ v.1 : ℝ) : ℂ) * Complex.I + (((m v.1).natAbs : ℕ) : ℂ) / 2))
        = ∏ v : {w : InfinitePlace K // ¬ w.IsReal},
            Complex.Gammaℂ (s + (((τ ((Equiv.subtypeEquivRight (fun w : InfinitePlace K => InfinitePlace.not_isReal_iff_isComplex) v).1) : ℝ) : ℂ) * Complex.I +
              (((m ((Equiv.subtypeEquivRight (fun w : InfinitePlace K => InfinitePlace.not_isReal_iff_isComplex) v).1)).natAbs : ℕ) : ℂ) / 2)) :=
          Fintype.prod_congr _ _ fun v => by rw [if_neg v.2, add_assoc]; rfl
      _ = ∏ j : {w : InfinitePlace K // w.IsComplex},
            Complex.Gammaℂ (s + (((τ j.1 : ℝ) : ℂ) * Complex.I + (((m j.1).natAbs : ℕ) : ℂ) / 2)) :=
          Equiv.prod_comp (Equiv.subtypeEquivRight fun w : InfinitePlace K => InfinitePlace.not_isReal_iff_isComplex)
            (fun j : {w : InfinitePlace K // w.IsComplex} =>
              Complex.Gammaℂ (s + (((τ j.1 : ℝ) : ℂ) * Complex.I + (((m j.1).natAbs : ℕ) : ℂ) / 2)))

theorem gamma'_eq_prod_subtype (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) (s : ℂ) :
    (∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)))
      = (∏ i : {w : InfinitePlace K // w.IsReal},
            Complex.Gammaℝ (s + (-(((τ i.1 : ℝ) : ℂ) * Complex.I) + signShift (((m i.1 : ℤ) : ZMod 2)))))
        * ∏ j : {w : InfinitePlace K // w.IsComplex},
            Complex.Gammaℂ (s + (-(((τ j.1 : ℝ) : ℂ) * Complex.I) + (((m j.1).natAbs : ℕ) : ℂ) / 2)) := by
  have h := gamma_eq_prod_subtype K (fun v => -τ v) m s
  have e1 : ∀ v : InfinitePlace K, (((-τ v : ℝ)) : ℂ) * Complex.I = -(((τ v : ℝ) : ℂ) * Complex.I) := by
    intro v; push_cast; ring
  simp only [e1, ← sub_eq_add_neg] at h
  rw [h]

end ArchPins

end F1Z

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.ArchPlace
open scoped Classical
namespace F1Z

section LevelProduct

variable (K : Type) [Field K] [NumberField K]

open scoped nonZeroDivisors

theorem addCharLevel_psiLocal_nonneg (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ addCharLevel (psiLocal K v) := by
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal]
  exact FractionalIdeal.count_coe_nonneg K v _

theorem exists_finset_forall_addCharLevel_psiLocal_eq_zero :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ v, v ∉ T → addCharLevel (psiLocal K v) = 0 := by
  have h := FractionalIdeal.finite_factors (K := K) ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
  rw [Filter.eventually_cofinite] at h
  refine ⟨h.toFinset, fun v hv => ?_⟩
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal]
  by_contra hne
  exact hv (h.mem_toFinset.2 hne)

theorem natAbs_discr_eq_prod_absNorm_pow_addCharLevel (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v, v ∉ T → addCharLevel (psiLocal K v) = 0) :
    (((discr K).natAbs : ℕ) : ℝ)
      = ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (addCharLevel (psiLocal K v)).toNat := by
  classical
  set D : Ideal (𝓞 K) := differentIdeal ℤ (𝓞 K) with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact differentIdeal_ne_bot

  have hexp : ∀ v : HeightOneSpectrum (𝓞 K),
      (addCharLevel (psiLocal K v)).toNat = (Associates.mk v.asIdeal).count (Associates.mk D).factors := by
    intro v
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal, ← hD,
      FractionalIdeal.count_coe K v hD0, Int.toNat_natCast]

  have hfac : ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.maxPowDividing D = D :=
    Ideal.finprod_heightOneSpectrum_factorization hD0
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing D) ⊆ (T : Set _) := by
    intro v hv
    by_contra hvT
    apply hv
    show v.maxPowDividing D = 1
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, ← hexp v, hT v hvT]
    simp
  have hprod : D = ∏ v ∈ T, v.maxPowDividing D := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp, hfac]
  have hnorm : Ideal.absNorm D = ∏ v ∈ T, Ideal.absNorm v.asIdeal ^ (addCharLevel (psiLocal K v)).toNat := by
    rw [hprod, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow, hexp]
  rw [← NumberField.absNorm_differentIdeal K (𝓞 K), ← hD, hnorm]
  push_cast
  rfl

theorem psiLocal_eq_one_of_mem_integers_of_addCharLevel_eq_zero (v : HeightOneSpectrum (𝓞 K))
    (hv : addCharLevel (psiLocal K v) = 0) (z : v.adicCompletion K) (hz : z ∈ v.adicCompletionIntegers K) :
    psiLocal K v z = 1 :=
  LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v z hz

theorem forall_psiLocal_mul_eq_one_iff_of_addCharLevel_eq_zero (v : HeightOneSpectrum (𝓞 K))
    (hv : addCharLevel (psiLocal K v) = 0) (w : v.adicCompletion K) :
    (∀ z : v.adicCompletion K, z ∈ v.adicCompletionIntegers K → psiLocal K v (z * w) = 1) ↔
      w ∈ v.adicCompletionIntegers K := by
  constructor
  · intro h
    by_contra hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hw

    have hw0 : w ≠ 0 := by intro h0; rw [h0, map_zero] at hw; exact not_lt_zero hw
    have hvw0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
    have hexp1 : WithZero.exp 1 ≤ Valued.v w := by
      rw [← WithZero.exp_log hvw0] at hw ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hw
      exact WithZero.exp_le_exp.2 (by omega)

    set S : Set ℤ := {n : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → psiLocal K v x = 1} with hS
    have hlev : addCharLevel (psiLocal K v) = sSup S := rfl

    have h1 : (1 : ℤ) ∈ S := by
      intro x hx
      have hz : x * w⁻¹ ∈ v.adicCompletionIntegers K := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
        calc Valued.v x * (Valued.v w)⁻¹ ≤ WithZero.exp 1 * (Valued.v w)⁻¹ := mul_le_mul_left hx _
          _ ≤ Valued.v w * (Valued.v w)⁻¹ := mul_le_mul_left hexp1 _
          _ = 1 := mul_inv_cancel₀ hvw0
      have := h (x * w⁻¹) hz
      rwa [inv_mul_cancel_right₀ hw0] at this

    have hbdd : BddAbove S := by
      obtain ⟨x₀, hx₀⟩ := AddChar.ne_one_iff.1 (LanglandsTunnell.TateLocal.psiLocal_ne_one K v)
      have hx₀0 : x₀ ≠ 0 := by intro h0; apply hx₀; rw [h0, AddChar.map_zero_eq_one]
      have hvx₀ : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).2 hx₀0
      refine ⟨WithZero.log (Valued.v x₀), fun n hn => ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      apply hx₀
      apply hn x₀
      rw [← WithZero.exp_log hvx₀]
      exact WithZero.exp_le_exp.2 hlt.le
    have : (1 : ℤ) ≤ addCharLevel (psiLocal K v) := by rw [hlev]; exact le_csSup hbdd h1
    rw [hv] at this
    exact absurd this (by norm_num)
  · intro hw z hz
    exact LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers K v (z * w) (mul_mem hz hw)

end LevelProduct

end F1Z

namespace F1Z
namespace NPAux

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

theorem norm_ext (w : InfinitePlace K) (x : w.Completion) : ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem exists_extensionEmbedding_eq_ofReal (w : InfinitePlace K) (r : ℝ) :
    ∃ x : w.Completion, extensionEmbedding w x = (r : ℂ) := by
  by_cases hw : w.IsReal
  · obtain ⟨x, hx⟩ := (bijective_extensionEmbeddingOfIsReal hw).2 r
    exact ⟨x, by rw [← extensionEmbeddingOfIsReal_apply hw, hx]⟩
  · have hc : w.IsComplex := not_isReal_iff_isComplex.1 hw
    exact ⟨(ringEquivComplexOfIsComplex hc).symm r, by
      rw [← ringEquivComplexOfIsComplex_apply hc, RingEquiv.apply_symm_apply]⟩

theorem ideleNorm_archUnitHom (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  have h1 : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)).erase w,
      ‖((archUnitHom w x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = 1 := by
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) v‖ ^ v.mult = 1
    rw [Function.update_of_ne hvw]
    change ‖(1 : v.Completion)‖ ^ v.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one h1, one_mul]
  show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) w‖ ^ w.mult = _
  rw [Function.update_self]

theorem tau_eq (τ₀ : ℝ) (τ : InfinitePlace K → ℝ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (extensionEmbedding v (x : v.Completion)).re → (extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar (normPowChar K τ₀) v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (v : InfinitePlace K) : τ v = τ₀ := by
  by_contra hne
  have hmult : (0 : ℝ) < (v.mult : ℝ) := by exact_mod_cast NumberField.InfinitePlace.mult_pos
  have hd : (τ v - τ₀) * (v.mult : ℝ) ≠ 0 := mul_ne_zero (sub_ne_zero.2 hne) hmult.ne'
  set t : ℝ := ((τ v - τ₀) * (v.mult : ℝ))⁻¹ with ht
  obtain ⟨x₀, hx₀⟩ := exists_extensionEmbedding_eq_ofReal v (Real.exp t)
  have hx₀0 : x₀ ≠ 0 := by
    intro h; rw [h, map_zero] at hx₀
    exact (Real.exp_pos t).ne' (by exact_mod_cast hx₀.symm)
  set x : (v.Completion)ˣ := Units.mk0 x₀ hx₀0 with hx
  have hex : extensionEmbedding v (x : v.Completion) = (Real.exp t : ℂ) := hx₀
  have hre : 0 < (extensionEmbedding v (x : v.Completion)).re := by rw [hex, Complex.ofReal_re]; exact Real.exp_pos t
  have him : (extensionEmbedding v (x : v.Completion)).im = 0 := by rw [hex, Complex.ofReal_im]
  have h := hτ v x hre him
  have hN : ideleNorm K (archUnitHom v x) = Real.exp ((v.mult : ℝ) * t) := by
    rw [ideleNorm_archUnitHom, ← norm_ext, hex, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
      ← Real.exp_nat_mul]
  have hL : ((archLocalChar (normPowChar K τ₀) v x : ℂˣ) : ℂ) =
      ((ideleNorm K (archUnitHom v x) : ℝ) : ℂ) ^ (Complex.I * (τ₀ : ℂ)) := rfl
  rw [hL, hN, Complex.ofReal_exp] at h

  have hlog : Complex.log (Complex.exp (((v.mult : ℝ) * t : ℝ) : ℂ)) = (((v.mult : ℝ) * t : ℝ) : ℂ) := by
    rw [Complex.log_exp] <;> simp [Real.pi_pos.le, Real.pi_pos]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), hlog] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h4 : ((((v.mult : ℝ) * t * (τ₀ - τ v) : ℝ)) : ℂ) * Complex.I = ((n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    push_cast at hn ⊢
    linear_combination hn
  have h5 : (v.mult : ℝ) * t * (τ₀ - τ v) = n * (2 * Real.pi) := by
    have := mul_right_cancel₀ Complex.I_ne_zero h4
    exact_mod_cast this
  have h6 : (v.mult : ℝ) * t * (τ₀ - τ v) = -1 := by
    rw [ht]; field_simp; ring
  have h7 : (n : ℝ) * (2 * Real.pi) = -1 := by rw [← h5, h6]
  have h8 : n ≠ 0 := by
    rintro rfl; simp at h7
  have h9 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs h8
  have h10 : |(n : ℝ) * (2 * Real.pi)| = 1 := by rw [h7]; simp
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h10
  nlinarith [Real.pi_gt_three]

theorem shift_eq_zero (τ₀ : ℝ) (m : InfinitePlace K → ℤ)
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ), ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar (normPowChar K τ₀) v x : ℂˣ) : ℂ) = (extensionEmbedding v (x : v.Completion)) ^ (m v))
    (v : InfinitePlace K) :
    (if v.IsReal then Complex.Gammaℝ else Complex.Gammaℂ) = (if v.IsReal then Complex.Gammaℝ else Complex.Gammaℂ) ∧
    ((v.IsReal → (m v).natAbs % 2 = 0) ∧ (¬ v.IsReal → m v = 0)) := by
  refine ⟨rfl, ?_, ?_⟩
  ·
    have hone : ∀ x : (v.Completion)ˣ, ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        (extensionEmbedding v (x : v.Completion)) ^ (m v) = 1 := by
      intro x hx
      rw [← hm v x hx]
      show ((ideleNorm K (archUnitHom v x) : ℝ) : ℂ) ^ (Complex.I * (τ₀ : ℂ)) = 1
      rw [ideleNorm_archUnitHom, ← norm_ext, hx, one_pow, Complex.ofReal_one, Complex.one_cpow]
    intro hv
    obtain ⟨x₀, hx₀⟩ := exists_extensionEmbedding_eq_ofReal v (-1)
    have hx₀0 : x₀ ≠ 0 := by
      intro h; rw [h, map_zero] at hx₀; norm_num at hx₀
    have h := hone (Units.mk0 x₀ hx₀0) (by rw [Units.val_mk0, hx₀]; simp)
    rw [Units.val_mk0, hx₀] at h
    have heven : Even (m v) := by
      rcases Int.even_or_odd (m v) with he | ho
      · exact he
      · exfalso
        rw [show ((-1 : ℝ) : ℂ) = -1 by push_cast; ring, ho.neg_one_zpow] at h
        norm_num at h
    have : Even (m v).natAbs := Int.natAbs_even.2 heven
    exact Nat.even_iff.1 this
  · have hone : ∀ x : (v.Completion)ˣ, ‖extensionEmbedding v (x : v.Completion)‖ = 1 →
        (extensionEmbedding v (x : v.Completion)) ^ (m v) = 1 := by
      intro x hx
      rw [← hm v x hx]
      show ((ideleNorm K (archUnitHom v x) : ℝ) : ℂ) ^ (Complex.I * (τ₀ : ℂ)) = 1
      rw [ideleNorm_archUnitHom, ← norm_ext, hx, one_pow, Complex.ofReal_one, Complex.one_cpow]
    intro hv
    have hc : v.IsComplex := not_isReal_iff_isComplex.1 hv

    by_contra hne
    have hd : ((m v : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
    set θ : ℝ := ((m v : ℤ) : ℝ)⁻¹ with hθ
    set ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hζ
    have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
    have hζ1 : ‖ζ‖ = 1 := by simp [hζ, Complex.norm_exp_ofReal_mul_I]
    set u : (v.Completion)ˣ := Units.mk0 ((ringEquivComplexOfIsComplex hc).symm ζ)
      (by intro h; apply hζ0; simpa using congrArg (ringEquivComplexOfIsComplex hc) h) with hu
    have heu : extensionEmbedding v (u : v.Completion) = ζ := by
      rw [← ringEquivComplexOfIsComplex_apply hc]; exact (ringEquivComplexOfIsComplex hc).apply_symm_apply ζ
    have h1 := hone u (by rw [heu, hζ1])
    rw [heu, hζ, ← Complex.exp_int_mul] at h1
    have h3 : ((m v : ℤ) : ℂ) * ((θ : ℂ) * Complex.I) = Complex.I := by
      have : ((m v : ℤ) : ℝ) * θ = 1 := mul_inv_cancel₀ hd
      have h4 : (((m v : ℤ) : ℝ) : ℂ) * ((θ : ℝ) : ℂ) = 1 := by exact_mod_cast this
      push_cast at h4 ⊢
      linear_combination Complex.I * h4
    rw [h3] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    have him := congrArg Complex.im hn
    simp only [Complex.I_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero,
      add_zero, mul_one] at him
    have hpos : (0 : ℝ) < (n : ℝ) := by nlinarith [Real.pi_pos]
    have hn1 : (1 : ℤ) ≤ n := by have := Int.cast_pos.1 hpos; omega
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    nlinarith [Real.pi_gt_three]

theorem prod_ite_isReal (f g : ℂ) :
    ∏ v : InfinitePlace K, (if v.IsReal then f else g) = f ^ nrRealPlaces K * g ^ nrComplexPlaces K := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  · rw [nrRealPlaces, Fintype.card_subtype]
  · rw [nrComplexPlaces, Fintype.card_subtype]
    congr 1
    ext v
    simp [not_isReal_iff_isComplex]

end F1Z.NPAux

namespace F1Z

open F1Z.NPAux in
theorem normPow_branch (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
    (τ₀ : ℝ) (hχ : χ = normPowChar K τ₀) :
    ∃ (Z : ℂ → ℂ) (A ε : ℂ), Differentiable ℂ Z ∧ A ≠ 0 ∧ ‖ε‖ = 1 ∧
      (∀ s : ℂ, 1 < s.re →
        Z s = A * ((s + ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) *
          ((∏ v : InfinitePlace K,
              (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
                else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))) *
            ∏' v : HeightOneSpectrum (𝓞 K),
              (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
                (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)))) ∧
      (∀ s : ℂ, 1 < s.re →
        Z (1 - s) = A * ε * ((((discr K).natAbs : ℕ) : ℂ) ^ (s - 1 / 2)) *
          ((s - ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) + ((τ₀ : ℝ) : ℂ) * Complex.I)) *
            ((∏ v : InfinitePlace K,
                (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
                  else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))) *
              ∏' v : HeightOneSpectrum (𝓞 K),
                (1 - (if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)))) := by
  subst hχ
  have hτv : ∀ v, τ v = τ₀ := tau_eq τ₀ τ hτ
  have hmv := fun v => (shift_eq_zero τ₀ m hm v).2
  have hre : ∀ w : ℂ, (w + (τ₀ : ℂ) * Complex.I).re = w.re := by intro w; simp
  have hre' : ∀ w : ℂ, (w - (τ₀ : ℂ) * Complex.I).re = w.re := by intro w; simp

  have hγ : ∀ s : ℂ, (∏ v : InfinitePlace K,
      (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))) =
      Complex.Gammaℝ (s + (τ₀ : ℂ) * Complex.I) ^ NumberField.InfinitePlace.nrRealPlaces K *
        Complex.Gammaℂ (s + (τ₀ : ℂ) * Complex.I) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    intro s
    rw [← prod_ite_isReal]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : v.IsReal
    · rw [if_pos hv, if_pos hv, hτv v, (hmv v).1 hv]; simp
    · rw [if_neg hv, if_neg hv, hτv v, (hmv v).2 hv]; simp
  have hγ' : ∀ s : ℂ, (∏ v : InfinitePlace K,
      (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))) =
      Complex.Gammaℝ (s - (τ₀ : ℂ) * Complex.I) ^ NumberField.InfinitePlace.nrRealPlaces K *
        Complex.Gammaℂ (s - (τ₀ : ℂ) * Complex.I) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
    intro s
    rw [← prod_ite_isReal]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : v.IsReal
    · rw [if_pos hv, if_pos hv, hτv v, (hmv v).1 hv]; simp
    · rw [if_neg hv, if_neg hv, hτv v, (hmv v).2 hv]; simp

  have hNv : ∀ v : HeightOneSpectrum (𝓞 K), (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ≠ 0 := by
    intro v
    have h1 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast h1
  have hcoef := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K τ₀
  have hunr : ∀ v : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt (normPowChar K τ₀) v := by
    intro v
    by_contra h
    have h2 := hcoef v
    rw [if_neg h] at h2
    exact absurd h2.symm (Complex.cpow_ne_zero_iff.2 (Or.inl (hNv v)))
  have hP : ∀ s : ℂ, 1 < s.re → (∏' v : HeightOneSpectrum (𝓞 K),
      (1 - (if IsUnramifiedCharAt (normPowChar K τ₀) v then ((normPowChar K τ₀ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) = NumberField.dedekindZeta K (s + (τ₀ : ℂ) * Complex.I) := by
    intro s hs
    have e1 : ∀ v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt (normPowChar K τ₀) v then ((normPowChar K τ₀ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
        (1 - (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-(s + (τ₀ : ℂ) * Complex.I)))⁻¹ := by
      intro v
      rw [hcoef v, ← Complex.cpow_add _ _ (hNv v)]
      congr 2; ring
    rw [tprod_congr e1]
    exact (NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K (s + (τ₀ : ℂ) * Complex.I)
      (by rw [hre]; exact hs)).tprod_eq
  have hP' : ∀ s : ℂ, 1 < s.re → (∏' v : HeightOneSpectrum (𝓞 K),
      (1 - (if IsUnramifiedCharAt (normPowChar K τ₀) v then (((normPowChar K τ₀ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) = NumberField.dedekindZeta K (s - (τ₀ : ℂ) * Complex.I) := by
    intro s hs
    have e1 : ∀ v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt (normPowChar K τ₀) v then (((normPowChar K τ₀ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
        (1 - (((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-(s - (τ₀ : ℂ) * Complex.I)))⁻¹ := by
      intro v
      have h1 := hcoef v
      rw [if_pos (hunr v)] at h1
      rw [if_pos (hunr v), Units.val_inv_eq_inv_val, h1, ← Complex.cpow_neg, ← Complex.cpow_add _ _ (hNv v)]
      congr 2; ring
    rw [tprod_congr e1]
    exact (NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K (s - (τ₀ : ℂ) * Complex.I)
      (by rw [hre']; exact hs)).tprod_eq

  obtain ⟨Λ, -, hΛfe, hΛf, ⟨ξ, hξd, hξ, -⟩, -, -⟩ := NumberField.exists_completedDedekindZeta_package K
  set d : ℂ := (((|NumberField.discr K| : ℤ) : ℂ)) with hd
  have hdpos : (0 : ℝ) < ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast abs_pos.2 (NumberField.discr_ne_zero K)
  have hd0 : d ≠ 0 := by rw [hd]; exact_mod_cast (abs_ne_zero.2 (NumberField.discr_ne_zero K))
  have hdR : d = ((((|NumberField.discr K| : ℤ) : ℝ)) : ℂ) := by rw [hd]; norm_cast
  have hdn : (((discr K).natAbs : ℕ) : ℂ) = d := by
    rw [hd, ← Int.cast_natCast, Int.natCast_natAbs]
  have hshift : Differentiable ℂ (fun s : ℂ => s + (τ₀ : ℂ) * Complex.I) := differentiable_id.add (differentiable_const _)
  refine ⟨fun s => ξ (s + (τ₀ : ℂ) * Complex.I) * d ^ (-(s + (τ₀ : ℂ) * Complex.I) / 2), 1,
    d ^ (-((τ₀ : ℂ) * Complex.I)), ?_, one_ne_zero, ?_, ?_, ?_⟩
  · exact (hξd.comp hshift).mul (Differentiable.const_cpow ((hshift.neg).div_const _) (Or.inl hd0))
  · rw [hdR, Complex.norm_cpow_eq_rpow_re_of_pos hdpos]; simp
  · intro s hs
    have hu : 1 < (s + (τ₀ : ℂ) * Complex.I).re := by rw [hre]; exact hs
    have hu0 : s + (τ₀ : ℂ) * Complex.I ≠ 0 := by
      intro h; have h' := congrArg Complex.re h; rw [hre] at h'; simp at h'; linarith
    have hu1 : s + (τ₀ : ℂ) * Complex.I ≠ 1 := by
      intro h; have h' := congrArg Complex.re h; rw [hre] at h'; simp at h'; linarith
    show ξ (s + (τ₀ : ℂ) * Complex.I) * d ^ (-(s + (τ₀ : ℂ) * Complex.I) / 2) = _
    rw [hγ s, hP s hs, hξ _ hu0 hu1, hΛf _ hu, one_mul]
    have hdd : d ^ ((s + (τ₀ : ℂ) * Complex.I) / 2) * d ^ (-(s + (τ₀ : ℂ) * Complex.I) / 2) = 1 := by
      rw [← Complex.cpow_add _ _ hd0, neg_div, add_neg_cancel, Complex.cpow_zero]
    set u := s + (τ₀ : ℂ) * Complex.I with hu'
    have hs1 : s - (1 - (τ₀ : ℂ) * Complex.I) = u - 1 := by rw [hu']; ring
    rw [hs1]
    calc u * (u - 1) * (d ^ (u / 2) * Complex.Gammaℝ u ^ NumberField.InfinitePlace.nrRealPlaces K *
            Complex.Gammaℂ u ^ NumberField.InfinitePlace.nrComplexPlaces K * NumberField.dedekindZeta K u) * d ^ (-u / 2)
        = u * ((u - 1) * (Complex.Gammaℝ u ^ NumberField.InfinitePlace.nrRealPlaces K * Complex.Gammaℂ u ^ NumberField.InfinitePlace.nrComplexPlaces K *
            NumberField.dedekindZeta K u)) * (d ^ (u / 2) * d ^ (-u / 2)) := by ring
      _ = _ := by rw [hdd, mul_one]
  · intro s hs
    have hu : 1 < (s - (τ₀ : ℂ) * Complex.I).re := by rw [hre']; exact hs
    have hu0 : s - (τ₀ : ℂ) * Complex.I ≠ 0 := by
      intro h; have h' := congrArg Complex.re h; rw [hre'] at h'; simp at h'; linarith
    have hu1 : s - (τ₀ : ℂ) * Complex.I ≠ 1 := by
      intro h; have h' := congrArg Complex.re h; rw [hre'] at h'; simp at h'; linarith
    have h1u0 : 1 - (s - (τ₀ : ℂ) * Complex.I) ≠ 0 := sub_ne_zero.2 (Ne.symm hu1)
    have h1u1 : 1 - (s - (τ₀ : ℂ) * Complex.I) ≠ 1 := by
      intro h; apply hu0; linear_combination -h
    show ξ (1 - s + (τ₀ : ℂ) * Complex.I) * d ^ (-(1 - s + (τ₀ : ℂ) * Complex.I) / 2) = _
    rw [hγ' s, hP' s hs, hdn, one_mul]
    have e1 : 1 - s + (τ₀ : ℂ) * Complex.I = 1 - (s - (τ₀ : ℂ) * Complex.I) := by ring
    rw [e1, hξ _ h1u0 h1u1, hΛfe _ hu0 hu1, hΛf _ hu]
    set u := s - (τ₀ : ℂ) * Complex.I with hu'
    have hs1 : s - (1 + (τ₀ : ℂ) * Complex.I) = u - 1 := by rw [hu']; ring
    rw [hs1]

    have hdpow : d ^ (u / 2) * d ^ (-(1 - u) / 2) = d ^ (-((τ₀ : ℂ) * Complex.I)) * d ^ (s - 1 / 2) := by
      rw [← Complex.cpow_add _ _ hd0, ← Complex.cpow_add _ _ hd0]
      congr 1; rw [hu']; ring
    calc (1 - u) * (1 - u - 1) * (d ^ (u / 2) * Complex.Gammaℝ u ^ NumberField.InfinitePlace.nrRealPlaces K *
            Complex.Gammaℂ u ^ NumberField.InfinitePlace.nrComplexPlaces K * NumberField.dedekindZeta K u) * d ^ (-(1 - u) / 2)
        = (d ^ (u / 2) * d ^ (-(1 - u) / 2)) * (u * ((u - 1) *
            (Complex.Gammaℝ u ^ NumberField.InfinitePlace.nrRealPlaces K * Complex.Gammaℂ u ^ NumberField.InfinitePlace.nrComplexPlaces K *
              NumberField.dedekindZeta K u))) := by ring
      _ = _ := by rw [hdpow]; try ring

end F1Z

namespace F1Z

section HeckeBridge

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.Converse LanglandsTunnell.HeckeTate NumberField.StandardAddChar NumberField.AdelicLevel Polynomial

variable (K : Type) [Field K] [NumberField K]

theorem continuous_of_continuous_coe (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((χ x : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.mpr ⟨hχ, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hχ.inv₀ fun x => (χ x).ne_zero

theorem valued_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    Valued.v (t : v.adicCompletion K) = 1 ↔
      ((t : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
        ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val,
    map_inv₀]
  constructor
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h1, h2⟩
    have hpos : 0 < Valued.v (t : v.adicCompletion K) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 t.ne_zero)
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)

theorem hasConductorExponentAt_congr (v : HeightOneSpectrum (𝓞 K)) {χ₁ χ₂ : (v.adicCompletion K)ˣ →* ℂˣ}
    (h : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ₁ u = χ₂ u) (c : ℕ) :
    HasConductorExponentAt K v χ₁ c ↔ HasConductorExponentAt K v χ₂ c := by
  unfold HasConductorExponentAt
  have hu : ∀ n, ∀ u ∈ higherUnitsAt K v n, χ₁ u = χ₂ u := fun n u hu => h u hu.1
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun u hu' => by rw [← hu c u hu']; exact h1 u hu',
      fun m hm => by obtain ⟨u, hu', hne⟩ := h2 m hm; exact ⟨u, hu', by rwa [← hu m u hu']⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun u hu' => by rw [hu c u hu']; exact h1 u hu',
      fun m hm => by obtain ⟨u, hu', hne⟩ := h2 m hm; exact ⟨u, hu', by rwa [hu m u hu']⟩⟩

theorem conductorExponentAt_congr (v : HeightOneSpectrum (𝓞 K)) {χ₁ χ₂ : (v.adicCompletion K)ˣ →* ℂˣ}
    (h : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ₁ u = χ₂ u) :
    conductorExponentAt K v χ₁ = conductorExponentAt K v χ₂ := by
  unfold conductorExponentAt
  congr 1
  ext c
  exact hasConductorExponentAt_congr K v h c

theorem isUnramifiedCharAt_iff_hasConductorExponentAt_zero (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedCharAt χ v ↔ HasConductorExponentAt K v (localChar χ v) 0 := by
  rw [hasConductorExponentAt_zero_iff]
  constructor
  · intro h u hu
    exact h u ((valued_eq_one_iff K v u).1 hu).1 ((valued_eq_one_iff K v u).1 hu).2
  · intro h u h1 h2
    exact h u ((valued_eq_one_iff K v u).2 ⟨h1, h2⟩)

open scoped Classical in

noncomputable def conductorOf (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal : ℝ) ^
    (((if v ∈ S then (conductorExponentAt K v (ρ v) : ℤ) else 0)) + addCharLevel (psiLocal K v))

theorem conductorOf_pos (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) : 0 < conductorOf K S ρ := by
  unfold conductorOf
  refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => ?_
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero h0
  exact zpow_pos hq _

open scoped Classical in
theorem heckeConductor_eq_conductorOf (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v)
    (hram : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar χ v u = ρ v u) :
    heckeConductor K χ = conductorOf K S ρ := by
  unfold heckeConductor conductorOf pinnedExp
  refine finprod_congr fun v => ?_
  congr 1
  by_cases hv : v ∈ S
  · rw [if_pos hv, conductorExponentAt_congr K v (fun u hu => hram v hv u ((valued_eq_one_iff K v u).1 hu).1
      ((valued_eq_one_iff K v u).1 hu).2)]
  · rw [if_neg hv, conductorExponentAt_eq_of_hasConductorExponentAt K v
      ((isUnramifiedCharAt_iff_hasConductorExponentAt_zero K χ v).1 (hunr v hv))]
    simp

theorem norm_heckeRootNumber (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hadm : IsAdmissibleTwist K χ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    ‖heckeRootNumber K χ aR kC‖ = 1 := by
  have hχu : IsUnitaryChar (𝓞 K) K χ := hadm.2.2
  unfold heckeRootNumber
  rw [norm_mul, norm_mul]
  have h1 : ‖(Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod (fun w => signEpsilon (aR w.1 w.2))‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun w _ => by
      unfold signEpsilon
      split_ifs <;> simp
  have h2 : ‖(Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod (fun w => Complex.I ^ (kC w.1 w.2).natAbs)‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one fun w _ => by rw [norm_pow, Complex.norm_I, one_pow]
  have hfin := (finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero K χ hadm).1
  have h3 : ‖∏ᶠ v : HeightOneSpectrum (𝓞 K), stdRootNumberAt K v (localChar χ v)‖ = 1 := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by
      intro v hv
      rw [Set.Finite.coe_toFinset]
      exact hv), norm_prod]
    refine Finset.prod_eq_one fun v _ => ?_
    have hu : ‖(localChar χ v (uniformizerUnit K v) : ℂ)‖ = 1 := by
      rw [localChar_apply]; exact hχu _
    by_cases h0 : HasConductorExponentAt K v (localChar χ v) 0
    · have h := stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v 1 (localChar χ v) 0
        (hasConductorExponentAt_one_zero K v) h0 (by rw [MonoidHom.one_apply, Units.val_one, norm_one]) hu
        (psiLocal_ne_one K v)
      have e1 : (1 : (v.adicCompletion K)ˣ →* ℂˣ) * localChar χ v = localChar χ v := by ext; simp
      rw [e1, stdRootNumberAt_one, mul_one] at h
      rw [h, norm_zpow, hu, one_zpow]
    ·
      obtain ⟨c, hc⟩ := exists_hasConductorExponentAt_of_continuous K v (localChar χ v)
        (continuous_localChar χ hadm.2.1 v)
      have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 fun h => h0 (h ▸ hc)
      exact norm_stdRootNumberAt_eq_one K v (localChar χ v) c hc1 hc hu
  rw [h1, h2, h3, one_mul, one_mul]

end HeckeBridge

end F1Z

namespace F1Z

section DatumBridge

p2m_open "NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.Converse LanglandsTunnell.HeckeTate Polynomial NumberField.InfinitePlace.Completion Complex"

variable (K : Type) [Field K] [NumberField K]

theorem multiset_prod_map_sum_singleton {α : Type} (s : Finset α) (f : α → ℂ) (g : ℂ → ℂ) :
    ((∑ w ∈ s, ({f w} : Multiset ℂ)).map g).prod = ∏ w ∈ s, g (f w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Multiset.map_add, Multiset.prod_add, Finset.prod_insert ha, ih,
      Multiset.map_singleton, Multiset.prod_singleton]

open scoped Classical in
theorem LFun_heckeDatum (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).LFun s = ∏' v : HeightOneSpectrum (𝓞 K),
      (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  unfold LDatum.LFun
  refine tprod_congr fun v => ?_
  simp only [heckeDatum]
  by_cases h : IsUnramifiedCharAt χ v
  · rw [if_pos h, if_pos h, eval_sub, eval_C, eval_mul, eval_C, eval_X]
  · rw [if_neg h, if_neg h, eval_C, zero_mul, sub_zero]

open scoped Classical in
theorem LFunDual_heckeDatum (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).LFunDual s = ∏' v : HeightOneSpectrum (𝓞 K),
      (1 - (if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  unfold LDatum.LFunDual
  refine tprod_congr fun v => ?_
  simp only [heckeDatum]
  by_cases h : IsUnramifiedCharAt χ v
  · rw [if_pos h, if_pos h, eval_sub, eval_C, eval_mul, eval_C, eval_X]
  · rw [if_neg h, if_neg h, eval_C, zero_mul, sub_zero]

open scoped Classical in
theorem archFactor_heckeDatum (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).archFactor s =
      (∏ i : {w : InfinitePlace K // w.IsReal}, Complex.Gammaℝ (s + (uR i.1 i.2 + signShift (aR i.1 i.2)))) *
        ∏ j : {w : InfinitePlace K // w.IsComplex}, Complex.Gammaℂ (s + (uC j.1 j.2 + ((kC j.1 j.2).natAbs : ℂ) / 2)) := by
  unfold LDatum.archFactor
  simp only [heckeDatum]
  rw [multiset_prod_map_sum_singleton, multiset_prod_map_sum_singleton]

open scoped Classical in
theorem archFactorDual_heckeDatum (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).archFactorDual s =
      (∏ i : {w : InfinitePlace K // w.IsReal}, Complex.Gammaℝ (s + (-uR i.1 i.2 + signShift (aR i.1 i.2)))) *
        ∏ j : {w : InfinitePlace K // w.IsComplex}, Complex.Gammaℂ (s + (-uC j.1 j.2 + ((kC j.1 j.2).natAbs : ℂ) / 2)) := by
  unfold LDatum.archFactorDual
  simp only [heckeDatum]
  rw [multiset_prod_map_sum_singleton, multiset_prod_map_sum_singleton]
  simp only [Int.natAbs_neg]

theorem isArchCompAt_real (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
    (w : InfinitePlace K) (hw : w.IsReal) :
    IsArchCompAt K χ w (((τ w : ℝ) : ℂ) * Complex.I) ((((m w : ℤ) : ZMod 2).val : ℕ) : ℤ) := by
  intro x
  have h := archPins_real K χ τ m hτ hm ⟨w, hw⟩ x
  have h' : ((archLocalChar χ w x : ℂˣ) : ℂ) = ((χ (archUnitHom w x) : ℂˣ) : ℂ) := rfl
  rw [h', h, coe_realCharFun_aux, zpow_natCast]
  have hy : ((Units.map (extensionEmbeddingOfIsReal hw).toMonoidHom x : ℝˣ) : ℝ) =
      extensionEmbeddingOfIsReal hw (x : w.Completion) := rfl
  rw [hy]
  have he : ((extensionEmbeddingOfIsReal hw (x : w.Completion) : ℝ) : ℂ) = extensionEmbedding w (x : w.Completion) :=
    extensionEmbeddingOfIsReal_apply hw _
  have hn : ‖extensionEmbeddingOfIsReal hw (x : w.Completion)‖ = ‖(x : w.Completion)‖ := by
    rw [← norm_ext_aux w (x : w.Completion), ← he, Complex.norm_real]
  rw [hn, he, InfinitePlace.mult, if_pos hw, Nat.cast_one, one_mul]

theorem isArchCompAt_complex (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
    (hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar χ v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
    (w : InfinitePlace K) (hw : w.IsComplex) :
    IsArchCompAt K χ w (((τ w : ℝ) : ℂ) * Complex.I) (m w) := by
  intro x
  have h := archPins_complex K χ τ m hτ hm ⟨w, hw⟩ x
  have h' : ((archLocalChar χ w x : ℂˣ) : ℂ) = ((χ (archUnitHom w x) : ℂˣ) : ℂ) := rfl
  rw [h', h, complexCharFun_apply]
  have hy : ((Units.map (extensionEmbedding w).toMonoidHom x : ℂˣ) : ℂ) = extensionEmbedding w (x : w.Completion) := rfl
  rw [anglePhase, hy, norm_ext_aux w (x : w.Completion), InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 hw),
    Nat.cast_ofNat]

end DatumBridge

end F1Z

namespace F1Z

section NormPowConductor

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.Converse LanglandsTunnell.HeckeTate NumberField.StandardAddChar

variable (K : Type) [Field K] [NumberField K]

theorem isUnramifiedCharAt_normPowChar (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) : IsUnramifiedCharAt (normPowChar K t) v := by
  by_contra h
  have h1 := ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg K t v
  rw [if_neg h] at h1
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast h0
  exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hq) |> fun h' => h' h1.symm)

open scoped Classical in

theorem conductorOf_eq_natAbs_discr (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (t : ℝ)
    (hram : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
      ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        localChar (normPowChar K t) v u = ρ v u) :
    conductorOf K S ρ = (((discr K).natAbs : ℕ) : ℝ) := by
  obtain ⟨T, hT⟩ := exists_finset_forall_addCharLevel_psiLocal_eq_zero K
  rw [natAbs_discr_eq_prod_absNorm_pow_addCharLevel K T hT]
  unfold conductorOf
  have hexp : ∀ v, ((if v ∈ S then (conductorExponentAt K v (ρ v) : ℤ) else 0) + addCharLevel (psiLocal K v))
      = addCharLevel (psiLocal K v) := by
    intro v
    by_cases hv : v ∈ S
    · rw [if_pos hv, ← conductorExponentAt_congr K v (fun u hu => hram v hv u ((valued_eq_one_iff K v u).1 hu).1
        ((valued_eq_one_iff K v u).1 hu).2), conductorExponentAt_eq_of_hasConductorExponentAt K v
        ((isUnramifiedCharAt_iff_hasConductorExponentAt_zero K (normPowChar K t) v).1 (isUnramifiedCharAt_normPowChar K t v))]
      simp
    · rw [if_neg hv, zero_add]
  simp only [hexp]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) (by
    intro v hv
    by_contra hvT
    exact hv (by show (Ideal.absNorm v.asIdeal : ℝ) ^ addCharLevel (psiLocal K v) = 1; rw [hT v hvT, zpow_zero]))]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← zpow_natCast]
  congr 1
  exact (Int.toNat_of_nonneg (addCharLevel_psiLocal_nonneg K v)).symm

end NormPowConductor

end F1Z

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.Converse LanglandsTunnell.HeckeTate F1Z in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ Nf : ℝ, 0 < Nf ∧
    ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
      (_hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (_hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ)
      (_hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v)
      (_hram : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar χ v u = ρ v u),
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    let P' : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    ∀ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
      (_hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
      (_hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)),
    let γ : ℂ → ℂ := fun s => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))
    let γ' : ℂ → ℂ := fun s => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))
    ((∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀) →
      ∃ (Z : ℂ → ℂ) (A ε : ℂ), Differentiable ℂ Z ∧ A ≠ 0 ∧ ‖ε‖ = 1 ∧
        (∀ s : ℂ, 1 < s.re → Z s = A * (γ s * P s)) ∧
        (∀ s : ℂ, 1 < s.re → Z (1 - s) = A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) * (γ' s * P' s))) ∧
    (∀ τ₀ : ℝ, χ = normPowChar K τ₀ →
      ∃ (Z : ℂ → ℂ) (A ε : ℂ), Differentiable ℂ Z ∧ A ≠ 0 ∧ ‖ε‖ = 1 ∧
        (∀ s : ℂ, 1 < s.re →
          Z s = A * ((s + ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ s * P s)))) ∧
        (∀ s : ℂ, 1 < s.re →
          Z (1 - s) = A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) *
            ((s - ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) + ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ' s * P' s))))) := by
  classical
  refine ⟨F1Z.conductorOf K S ρ, F1Z.conductorOf_pos K S ρ, ?_⟩
  intro χ hχc hχu hχF hunr hram P P' τ m hτ hm γ γ'
  have hχc' : Continuous χ := F1Z.continuous_of_continuous_coe K χ hχc
  constructor
  · intro hnp
    have hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1 := by
      by_contra h
      push_neg at h
      obtain ⟨t, ht⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles K χ hχc' hχu h
      exact hnp t ht
    have hadm : IsAdmissibleTwist K χ := ⟨hχF, hχc', hχu⟩
    set uR : ∀ w : InfinitePlace K, w.IsReal → ℂ := fun w _ => ((τ w : ℝ) : ℂ) * Complex.I with huR
    set aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2 := fun w _ => ((m w : ℤ) : ZMod 2) with haR
    set uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ := fun w _ => ((τ w : ℝ) : ℂ) * Complex.I with huC
    set kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ := fun w _ => m w with hkC
    have hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K χ w (uR w hw) ((aR w hw).val : ℤ) := fun w hw =>
      F1Z.isArchCompAt_real K χ τ m hτ hm w hw
    have hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K χ w (uC w hw) (kC w hw) := fun w hw =>
      F1Z.isArchCompAt_complex K χ τ m hτ hm w hw
    obtain ⟨-, -, -, Λ, Λd, hΛ, hΛd, -, -, h1, h2, hFE⟩ := isNicePinned_heckeDatum K χ hadm hχ1 uR aR uC kC hR hC
    have habs : ∀ s : ℂ, 1 < s.re → (heckeDatum K χ uR aR uC kC).abscissa < s.re := fun s hs => by
      show (1 : ℝ) < s.re; exact hs
    refine ⟨Λ, 1, heckeRootNumber K χ aR kC, hΛ, one_ne_zero, F1Z.norm_heckeRootNumber K χ hadm aR kC,
      fun s hs => ?_, fun s hs => ?_⟩
    · rw [h1 s (habs s hs), F1Z.archFactor_heckeDatum, F1Z.LFun_heckeDatum, one_mul, one_mul]
      simp only [γ, P, huR, haR, huC, hkC]
      rw [F1Z.gamma_eq_prod_subtype]
    · have hF := hFE (1 - s)
      have hc : ((heckeDatum K χ uR aR uC kC).center : ℝ) = 1 / 2 := rfl
      rw [hc] at hF
      have e1 : (((1 / 2 : ℝ)) : ℂ) - (1 - s) = s - 1 / 2 := by push_cast; ring
      have e2 : 2 * (((1 / 2 : ℝ)) : ℂ) - (1 - s) = s := by push_cast; ring
      rw [e1, e2, h2 s (habs s hs), F1Z.heckeConductor_eq_conductorOf K S ρ χ hunr hram, F1Z.archFactorDual_heckeDatum,
        F1Z.LFunDual_heckeDatum, one_mul] at hF
      rw [hF, one_mul]
      simp only [γ', P', huR, haR, huC, hkC]
      rw [F1Z.gamma'_eq_prod_subtype]
  · intro t ht
    obtain ⟨Z, A, ε, hZ, hA, hε, h1, h2⟩ := F1Z.normPow_branch K χ hχc hχu hχF τ m hτ hm t ht
    have hNf : (F1Z.conductorOf K S ρ : ℂ) = (((discr K).natAbs : ℕ) : ℂ) := by
      rw [F1Z.conductorOf_eq_natAbs_discr K S ρ t (fun v hv u h1' h2' => by rw [← ht]; exact hram v hv u h1' h2')]
      push_cast
      rfl
    refine ⟨Z, A, ε, hZ, hA, hε, fun s hs => ?_, fun s hs => ?_⟩
    · rw [h1 s hs]
    · rw [h2 s hs, hNf]

end S_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq (solution)
