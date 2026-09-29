-- Prove2me | solution 1 for LanglandsTunnell.exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a303abc7-37ac-5a57-8961-df30406c8c5d

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul
import Theorems.Thm_AutomorphicForm_eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_sq_mul_sq_eq_one_and_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
import Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
import Theorems.Thm_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
import Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
import Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne_of_torus_profile_eigen
import Theorems.Thm_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_weightOne_whittakerCoefficient_torus_eq_archW_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_ne_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace PIN

theorem exists_finset_norm_twist_b_eq_one
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0)
    (Θ : HeckeEigensystem ℚ ℂ) (hΘ : Θ.AgreesAwayFromFinite Φ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S₁ →
      ‖(Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b p‖ = 1 := by
  classical
  obtain ⟨S₀, hS₀⟩ :=
    LanglandsTunnell.exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
      c u d₁ d₂ T hd hcov Φ P archC dR dC hWF hP0
  obtain ⟨S₂, hS₂⟩ := hΘ
  refine ⟨S₀ ∪ S₂, fun p hp => ?_⟩
  have hp0 : p ∉ S₀ := fun h => hp (Finset.mem_union_left _ h)
  have hp2 : p ∉ S₂ := fun h => hp (Finset.mem_union_right _ h)
  have hN : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 p.ne_bot))
  rw [HeckeEigensystem.twist_b, (hS₂ p hp2).2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN _), hS₀ p hp0, ← Real.rpow_natCast,
    ← Real.rpow_mul hN.le, show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one,
    inv_mul_cancel₀ hN.ne']

end Ws47.PIN

namespace Ws47
namespace PIN
namespace CB

theorem psiQ_apply_single_real : ∀ (w : InfinitePlace ℚ), w.IsReal → ∀ x : InfiniteAdeleRing ℚ,
    (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      NumberField.StandardAddChar.psiQ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)) := by
  intro w hw x _
  rw [NumberField.StandardAddChar.psiQ_apply]
  rw [show ((⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ).2) = 0 from rfl, AddChar.map_zero_eq_one, mul_one,
      show ((⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ).1) = x from rfl,
      NumberField.StandardAddChar.psiArch_apply, finprod_eq_prod_of_fintype, Fintype.prod_subsingleton _ w,
      NumberField.StandardAddChar.psiArchPlace_apply]
  congr 1
  congr 1
  exact extensionEmbeddingOfIsReal_apply _ _

theorem psiQ_eq_stdAddChar : NumberField.StandardAddChar.psiQ = NumberField.StandardAddChar.stdAddChar ℚ := by
  exact AutomorphicForm.eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp ℚ _
    NumberField.StandardAddChar.isGlobalAddChar_psiQ Rat.infinitePlace Rat.isReal_infinitePlace
    (psiQ_apply_single_real _ Rat.isReal_infinitePlace)

theorem exists_mem_finiteAdelicGL2Subgroup_glFin_eq (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ g₀' : AdelicGL2 (𝓞 ℚ) ℚ, g₀' ∈ finiteAdelicGL2Subgroup ℚ ∧ glFin (𝓞 ℚ) ℚ g₀' = glFin (𝓞 ℚ) ℚ g₀ := by
  refine ⟨AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g₀), ?_, AdelicDock.glFin_finEmbed (𝓞 ℚ) ℚ _⟩
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ _

theorem hasArchCharacterAt₀_all_of_comp (n : ℤ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (h : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) :
    ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ := by
  intro w hw
  obtain rfl : Rat.infinitePlace = w := Subsingleton.elim _ _
  exact h

theorem exists_archTypeFamily_mem_one (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) :
    ∃ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys := by
  refine ⟨ArchTypeFamily.ofChar ℚ fun w' => (Subsingleton.elim Rat.infinitePlace w') ▸
    ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))), ?_⟩
  rw [mem_archCutSubmodule_ofChar_iff]
  intro w'
  obtain rfl : Rat.infinitePlace = w' := Subsingleton.elim _ _
  exact hφ

theorem exists_ofChar_mem_one (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) :
    ∃ χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ, φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
  refine ⟨fun w' => (Subsingleton.elim Rat.infinitePlace w') ▸
    ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))), ?_⟩
  rw [mem_archCutSubmodule_ofChar_iff]
  intro w'
  obtain rfl : Rat.infinitePlace = w' := Subsingleton.elim _ _
  exact hφ

theorem mem_isotypicCuspSubmodule' (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Ψ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Ψ φ) :
    φ ∈ isotypicCuspSubmodule ℚ (productionPinsGeneral ℚ) ξ N S Ψ := by
  exact hφ.mem_isotypicCuspSubmodule

end Ws47.PIN.CB

namespace Ws47
namespace PROJK
open NumberField.AdelicVolume

theorem archComponent_glArch_adelicArchGLInclAt_self {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (κ : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w κ)) = κ := by
  unfold adelicArchGLInclAt
  rw [MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_glArch_adelicArchGLInclAt_of_ne {F : Type} [Field F] [NumberField F] {v w : InfinitePlace F}
    (hvw : v ≠ w) (κ : GL (Fin 2) w.Completion) :
    archComponent F v (glArch (𝓞 F) F (adelicArchGLInclAt F w κ)) = 1 := by
  unfold adelicArchGLInclAt
  rw [MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne F hvw]

theorem mul_adelicArchGLInclAt_mem_centreCutSiegelSet {F : Type} [Field F] [NumberField F]
    {c u d₁ d₂ : ℝ} {w : InfinitePlace F} {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (κ : rowIsometrySubgroup₀ w.Completion) :
    g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) ∈ centreCutSiegelSet F c u d₁ d₂ := by
  obtain ⟨hfin, hh, hx, hd⟩ := hg
  have hκ : IsRowIsometry (κ : GL (Fin 2) w.Completion) := rowIsometrySubgroup₀_le _ κ.2
  have hcomp : ∀ v : InfinitePlace F, IsRowIsometry (archComponent F v (glArch (𝓞 F) F (adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)))) := by
    intro v
    by_cases hvw : v = w
    · subst hvw; rw [archComponent_glArch_adelicArchGLInclAt_self]; exact hκ
    · rw [archComponent_glArch_adelicArchGLInclAt_of_ne hvw]; exact isRowIsometry_one
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [map_mul, show glFin (𝓞 F) F (adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)) = 1 from
      glFin_adelicArchGLIncl F _, mul_one]
    exact hfin
  · rw [map_mul, map_mul, localHeight_mul_rowIsometry _ (hcomp v)]
    exact hh v
  · rw [map_mul, map_mul, xWindowSq_mul_rowIsometry _ (hcomp v)]
    exact hx v
  · unfold archDetNorm
    rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul, (hcomp v).1, mul_one]
    exact hd v

theorem mul_adelicArchGLInclAt_mem_iUnion_image_mul_centreCutSiegelSet {F : Type} [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hT : ∀ x ∈ T, glArch (𝓞 F) F x = 1)
    (w : InfinitePlace F) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (κ : rowIsometrySubgroup₀ w.Completion) :
    g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  simp only [Set.mem_iUnion, Set.mem_image] at hg ⊢
  obtain ⟨x, hxT, s, hs, rfl⟩ := hg
  refine ⟨x, hxT, s * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion),
    mul_adelicArchGLInclAt_mem_centreCutSiegelSet hs κ, ?_⟩

  have hcomm : adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) * x = x * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) := by
    refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
    · rw [map_mul, map_mul, hT x hxT, mul_one, one_mul]
    · rw [map_mul, map_mul, show glFin (𝓞 F) F (adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)) = 1 from
        glFin_adelicArchGLIncl F _, mul_one, one_mul]
  show s * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) * x = s * x * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)
  rw [mul_assoc, hcomm, ← mul_assoc]

end Ws47.PROJK

namespace Ws47
namespace PIN
namespace CB

open NumberField.AdelicVolume

theorem dz_realComponent_eq_coe {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    realComponent w hw g = ((archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; rfl

theorem dz_archRealProjAt_adelicArchGLInclAt {w : InfinitePlace ℚ} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    archRealProjAt hw (adelicArchGLInclAt ℚ w k) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw) k := by
  rw [← archRealGLAt_glEquivOfRingEquiv hw k, archRealProjAt_archRealGLAt]

theorem dz_glFin_adelicArchGLInclAt (w : InfinitePlace ℚ) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 ℚ) ℚ (adelicArchGLInclAt ℚ w k) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem dz_glFin_archRealGLAt {w : InfinitePlace ℚ} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem dz_archRealGLAt_eq {w : InfinitePlace ℚ} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = adelicArchGLInclAt ℚ w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) := rfl

theorem dz_archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 := by
  show ((((archWeightOneℝ r) ^ (0 : ℤ) : ℂˣ)) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

theorem dz_char_zero_comp (κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
    ((((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
        (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) κ : ℂˣ) : ℂ) = 1 := by
  rw [MonoidHom.comp_apply, dz_archWeightCharℝ_zero]

theorem dz_coe_glEquivOfRingEquiv {K L : Type*} [NormedField K] [NormedField L] (e : K ≃+* L) (k : GL (Fin 2) K) :
    ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = e.toRingHom.mapMatrix (k : Matrix (Fin 2) (Fin 2) K) := by
  ext i j; rfl

theorem dz_prod_archDetNorm_mul_adelicArchGLInclAt (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : GL (Fin 2) (Rat.infinitePlace).Completion)
    (hk : ‖((k : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion)).det‖ = 1) :
    ∏ v : InfinitePlace ℚ, archDetNorm v (g * adelicArchGLInclAt ℚ Rat.infinitePlace k) ^ v.mult =
      ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult := by
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  congr 1
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul, Ws47.PROJK.archComponent_glArch_adelicArchGLInclAt_self,
    hk, mul_one]

theorem dz_J_w_coe :
    ((glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
        (glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![(-1 : ℝ), 1] := by
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.apply_symm_apply, UpperHalfPlane.val_J]
  fin_cases i <;> fin_cases j <;> simp

theorem dz_norm_det_J_w :
    ‖(((glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J :
        GL (Fin 2) (Rat.infinitePlace).Completion)) : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion).det‖ = 1 := by
  rw [dz_coe_glEquivOfRingEquiv, ← RingHom.map_det, UpperHalfPlane.val_J, Matrix.det_fin_two_of]
  simp

theorem dz_char_one_comp (κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
    ((((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
        (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) κ : ℂˣ) : ℂ) =
      ((archWeightCharℝ 1 (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
        (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace) κ) : ℂˣ) : ℂ) := by
  rw [MonoidHom.comp_apply]

theorem fibre_weight_one
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂)
    (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hDW : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (z₁ : ℂ)
    (hfib : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ 1 g = archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) archC dR dC g * z₁) :
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ → ∀ κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ 1 (g * adelicArchGLInclAt ℚ Rat.infinitePlace (κ : GL (Fin 2) (Rat.infinitePlace).Completion))
        = (((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) κ : ℂ)
          * whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ 1 g := by
  set w : InfinitePlace ℚ := Rat.infinitePlace with hwdef
  have hw : w.IsReal := Rat.isReal_infinitePlace
  intro g hg κ
  have hfibK : glFin (𝓞 ℚ) ℚ (g * adelicArchGLInclAt ℚ w (κ : GL (Fin 2) w.Completion)) = glFin (𝓞 ℚ) ℚ g₀ := by
    rw [map_mul, dz_glFin_adelicArchGLInclAt, mul_one]; exact hg
  have harchWK : archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) archC dR dC
        (g * adelicArchGLInclAt ℚ w (κ : GL (Fin 2) w.Completion)) =
      ((archWeightCharℝ 1 (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) κ) : ℂˣ) : ℂ) *
        archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) archC dR dC g := by
    unfold archW
    rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ w, dif_pos hw, dif_pos hw,
      dz_realComponent_eq_coe, dz_realComponent_eq_coe, map_mul, dz_archRealProjAt_adelicArchGLInclAt]
    exact hDW w hw (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) κ)
      (archRealProjAt hw g)
  rw [hfib _ hfibK, hfib g hg, harchWK, dz_char_one_comp]
  ring

theorem dz_whittakerCoefficient_translate (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (h g : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ (fun y => φ (y * h)) 1 g =
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ 1 (g * h) := by
  letI := (productionPinsGeneral ℚ).nS
  simp only [whittakerCoefficient, mul_assoc]

theorem dz_whittakerIntegrand_integrable (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : Continuous φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    MeasureTheory.Integrable
      (fun x : AdeleRing (𝓞 ℚ) ℚ => φ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x)))
      (productionPinsGeneral ℚ).ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  have hcont : Continuous (fun x : AdeleRing (𝓞 ℚ) ℚ => φ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))) :=
    (hφ.comp (AutomorphicForm.continuous_unipotentGL2.mul continuous_const)).mul
      (hψ.comp ((continuous_const.mul continuous_id).neg))
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  show MeasureTheory.Integrable _ (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ))
  rw [ProbabilityTheory.cond]
  refine MeasureTheory.Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne')
  exact (hcont.continuousOn.integrableOn_compact hC).mono_set hsub

theorem dz_whittakerCoefficient_sub_smul_add (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (φ₁ φ₂ φ₃ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) (h₃ : Continuous φ₃) (c : ℂ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ (φ₁ - c • (φ₂ + φ₃)) 1 g =
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ₁ 1 g -
        c * (whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ₂ 1 g + whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ₃ 1 g) := by
  letI := (productionPinsGeneral ℚ).nS
  have h₁' := dz_whittakerIntegrand_integrable ψ hψ φ₁ h₁ g
  have h₂' := dz_whittakerIntegrand_integrable ψ hψ φ₂ h₂ g
  have h₃' := dz_whittakerIntegrand_integrable ψ hψ φ₃ h₃ g
  simp only [whittakerCoefficient]
  have hfun : (fun x : AdeleRing (𝓞 ℚ) ℚ => (φ₁ - c • (φ₂ + φ₃)) (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x)))
      = fun x => φ₁ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))
          - c * (φ₂ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))
            + φ₃ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))) := by
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have h23 : MeasureTheory.Integrable (fun x : AdeleRing (𝓞 ℚ) ℚ =>
      c * (φ₂ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))
        + φ₃ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x)))) (productionPinsGeneral ℚ).ν :=
    (h₂'.add h₃').const_mul c
  rw [hfun, MeasureTheory.integral_sub h₁' h23, MeasureTheory.integral_const_mul, MeasureTheory.integral_add h₂' h₃']

theorem dz_archW_eq (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archW (fun _ _ => P) archC dR dC g =
      (dR Rat.infinitePlace Rat.isReal_infinitePlace).W (realComponent Rat.infinitePlace Rat.isReal_infinitePlace g) := by
  unfold archW
  rw [Fintype.prod_subsingleton _ Rat.infinitePlace, dif_pos Rat.isReal_infinitePlace]

theorem dz_realComponent_mul_archRealGLAt {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) (m : GL (Fin 2) ℝ) :
    realComponent w hw (g * archRealGLAt hw m) = realComponent w hw g * (m : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [dz_realComponent_eq_coe, dz_realComponent_eq_coe, map_mul, archRealProjAt_archRealGLAt, Units.val_mul]

theorem dz_J_coe_eq_diagonal :
    ((UpperHalfPlane.J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![(-1 : ℝ), 1] := by
  rw [UpperHalfPlane.val_J]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem dz_diagonal_mul_self : Matrix.diagonal ![(-1 : ℝ), 1] * Matrix.diagonal ![(-1 : ℝ), 1] = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i; fin_cases i <;> simp

theorem device_on_fibre
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂)
    (hgen : ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))
    (htype : |(u₁ - u₂).re| < 1)
    (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (dR Rat.infinitePlace Rat.isReal_infinitePlace).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * (dR Rat.infinitePlace Rat.isReal_infinitePlace).W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : ArchCasimir.IsCasimirEigen (dR Rat.infinitePlace Rat.isReal_infinitePlace))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (x₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hsm : IsArchSmoothAt Rat.isReal_infinitePlace x₀) (hKf : IsKfSmooth ℚ x₀)
    (hx₀c : Continuous x₀) (hcont' : ∀ d : ArchDir, Continuous (archDerivAt Rat.isReal_infinitePlace d x₀))
    (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (z₁ : ℂ)
    (hfibx : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ x₀ 1 g = archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) archC dR dC g * z₁) :
    ∃ κ : ℂ, κ ^ 2 * (u₁ - u₂) ^ 2 = 1 ∧
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ
          (fun y => (archDerivAt Rat.isReal_infinitePlace ArchDir.H x₀
              - Complex.I • (archDerivAt Rat.isReal_infinitePlace ArchDir.E x₀ + archDerivAt Rat.isReal_infinitePlace ArchDir.Fm x₀))
                (y * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)) 1 g
        = κ⁻¹ * whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ x₀ 1 g := by
  set w : InfinitePlace ℚ := Rat.infinitePlace with hwdef
  have hw : w.IsReal := Rat.isReal_infinitePlace
  obtain ⟨κ, hκsq, hκ⟩ :=
    LanglandsTunnell.Converse.ArchDatumR.exists_sq_mul_sq_eq_one_and_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
      u₁ u₂ a₁ a₂ ha hu hgen htype (dR w hw) hDW hDE
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at hκsq
  refine ⟨κ, hκsq, fun g hg => ?_⟩
  set Jg : AdelicGL2 (𝓞 ℚ) ℚ := archRealGLAt hw UpperHalfPlane.J with hJg
  set g' : AdelicGL2 (𝓞 ℚ) ℚ := g * Jg with hg'def
  have hfibJ : ∀ y : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ (y * Jg) = glFin (𝓞 ℚ) ℚ y := fun y => by
    rw [map_mul, hJg, dz_glFin_archRealGLAt, mul_one]
  have hg' : glFin (𝓞 ℚ) ℚ g' = glFin (𝓞 ℚ) ℚ g₀ := by rw [hg'def, hfibJ, hg]

  have h1 : whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ
        (fun y => (archDerivAt hw ArchDir.H x₀ - Complex.I • (archDerivAt hw ArchDir.E x₀ + archDerivAt hw ArchDir.Fm x₀)) (y * Jg)) 1 g
      = whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ
          (archDerivAt hw ArchDir.H x₀ - Complex.I • (archDerivAt hw ArchDir.E x₀ + archDerivAt hw ArchDir.Fm x₀)) 1 g' :=
    dz_whittakerCoefficient_translate ψ _ Jg g

  have h2 := dz_whittakerCoefficient_sub_smul_add ψ hψ (archDerivAt hw ArchDir.H x₀) (archDerivAt hw ArchDir.E x₀)
    (archDerivAt hw ArchDir.Fm x₀) (hcont' _) (hcont' _) (hcont' _) Complex.I g'

  have hpins : productionPinsOf ℚ (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
      (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ) =
        productionPinsGeneral ℚ := rfl
  have hcomm := (LanglandsTunnell.isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
    (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) ψ hψ w hw x₀ hsm hKf 1).2.1
  rw [hpins] at hcomm
  have hflow : ∀ d : ArchDir, whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ (archDerivAt hw d x₀) 1 g' =
      ArchCasimir.matrixFlowDeriv d (dR w hw).W (realComponent w hw g') * z₁ := by
    intro d
    rw [← hcomm d]
    show deriv (fun t => whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ x₀ 1 (g' * archFlowAt hw d t)) 0 = _
    have hfun : (fun t => whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ x₀ 1 (g' * archFlowAt hw d t)) =
        fun t => (dR w hw).W (realComponent w hw g' * ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) * z₁ := by
      funext t
      have hfl : glFin (𝓞 ℚ) ℚ (g' * archFlowAt hw d t) = glFin (𝓞 ℚ) ℚ g₀ := by
        rw [map_mul, AutomorphicForm.archFlowAt, dz_glFin_archRealGLAt, mul_one, hg']
      rw [hfibx _ hfl, dz_archW_eq, AutomorphicForm.archFlowAt, dz_realComponent_mul_archRealGLAt]
    rw [hfun, deriv_mul_const_field]
    rfl

  have hX' : realComponent w hw g' = realComponent w hw g * Matrix.diagonal ![(-1 : ℝ), 1] := by
    rw [hg'def, hJg, dz_realComponent_mul_archRealGLAt, dz_J_coe_eq_diagonal]
  have hdet : (realComponent w hw g').det ≠ 0 := by
    rw [dz_realComponent_eq_coe, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Units.isUnit _).ne_zero
  have hrel := hκ (realComponent w hw g') hdet
  rw [hX', Matrix.mul_assoc, dz_diagonal_mul_self, Matrix.mul_one, ← hX'] at hrel

  rw [h1, h2, hflow, hflow, hflow, hfibx g hg, dz_archW_eq]
  rw [hrel]
  field_simp

theorem fibre_profile_eq_datum
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (x₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g₀' : AdelicGL2 (𝓞 ℚ) ℚ)
    (hg₀' : g₀' ∈ finiteAdelicGL2Subgroup ℚ) (z₁ : ℂ)
    (hfibx : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀' →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ x₀ 1 g = archW (fun _ _ => P) archC dR dC g * z₁)
    (Wr : InfinitePlace ℚ → ℂ → ℂ) (ρ' : ℂ)
    (hWr : ∀ (w : InfinitePlace ℚ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ), ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
      Wr w (extensionEmbedding w (((a : AdeleRing (𝓞 ℚ) ℚ)).1 w)) = ρ' * whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ x₀ 1 (diagOne a * g₀')) :
    ∀ t : ℝ, t ≠ 0 → Wr Rat.infinitePlace t = ρ' * z₁ * (dR Rat.infinitePlace Rat.isReal_infinitePlace).W (ArchR.diagOne t) := by
  set w : InfinitePlace ℚ := Rat.infinitePlace with hwdef
  have hw : w.IsReal := Rat.isReal_infinitePlace
  intro t ht
  have ht' : (ringEquivRealOfIsReal hw).symm t ≠ 0 := by
    intro h
    apply ht
    simpa using congrArg (ringEquivRealOfIsReal hw) h
  set tw : (w.Completion)ˣ := Units.mk0 ((ringEquivRealOfIsReal hw).symm t) ht' with htw
  set a : (AdeleRing (𝓞 ℚ) ℚ)ˣ := archCentralUnit ℚ w tw with hadef
  have h2 : ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 := archCentralUnit_snd w tw
  have h1 : ((a : AdeleRing (𝓞 ℚ) ℚ)).1 w = (ringEquivRealOfIsReal hw).symm t := by
    rw [hadef, archCentralUnit_fst_self]; rfl
  have hW := hWr w a h2
  have hemb : extensionEmbedding w (((a : AdeleRing (𝓞 ℚ) ℚ)).1 w) = (t : ℂ) := by
    rw [h1, ← extensionEmbeddingOfIsReal_apply hw]
    congr 1
    exact (ringEquivRealOfIsReal hw).apply_symm_apply t
  rw [hemb] at hW

  have hfinD : glFin (𝓞 ℚ) ℚ (diagOne a) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [glFin_apply, diagOne_coe_apply, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [h2] <;> rfl
  have hfib' : glFin (𝓞 ℚ) ℚ (diagOne a * g₀') = glFin (𝓞 ℚ) ℚ g₀' := by rw [map_mul, hfinD, one_mul]
  have hP0 : archRealProjAt hw g₀' = 1 := by
    unfold archRealProjAt
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, (mem_finiteAdelicGL2Subgroup_iff ℚ g₀').mp hg₀', map_one, map_one]
  have hreal : realComponent w hw (diagOne a * g₀') = ArchR.diagOne t := by
    rw [dz_realComponent_eq_coe, map_mul, hP0, mul_one]
    ext i j
    change ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
      (archComponent ℚ w (glArch (𝓞 ℚ) ℚ (diagOne a))) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = _
    rw [glEquivOfRingEquiv_apply_entry, archComponent_apply, glArch_apply, diagOne_coe_apply, ArchR.diagOne]
    fin_cases i <;> fin_cases j
    · simp [h1]
    · simp; rfl
    · simp; rfl
    · simp
      exact map_one _
  rw [hW, hfibx _ hfib', dz_archW_eq, hreal]
  ring

theorem stdWindow_mul_archIncl_mem (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ (productionPinsGeneral ℚ).D)
    (κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
    g * adelicArchGLInclAt ℚ Rat.infinitePlace (κ : GL (Fin 2) (Rat.infinitePlace).Completion) ∈ (productionPinsGeneral ℚ).D := by
  rw [productionPinsGeneral_D] at hg ⊢
  unfold classRepSiegelSet at hg ⊢
  refine Ws47.PROJK.mul_adelicArchGLInclAt_mem_iUnion_image_mul_centreCutSiegelSet _ _ _ _ _ (fun x hx => ?_)
    Rat.infinitePlace hg κ
  letI := Fintype.ofFinite (ClassGroup (𝓞 ℚ) ⧸ (classSq ℚ).range)
  rw [classRepTranslates, Finset.mem_map] at hx
  obtain ⟨C, -, rfl⟩ := hx
  exact glArch_classRepEmbedding ℚ C

theorem measurableSet_stdWindow :
    @MeasurableSet (AdelicGL2 (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 ℚ) ℚ) (productionPinsGeneral ℚ).D := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  rw [productionPinsGeneral_D]
  unfold classRepSiegelSet
  refine Finset.measurableSet_biUnion _ fun x _ => ?_
  have himage : (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2 = (· * x⁻¹) ⁻¹' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2 := by
    ext g
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩; simpa using hs
    · intro h; exact ⟨g * x⁻¹, h, by simp⟩
  rw [himage]
  exact (measurableSet_centreCutSiegelSet (F := ℚ) _ _ _ _).preimage (continuous_mul_const _).measurable

end Ws47.PIN.CB

namespace Ws47
namespace AD5
open MeasureTheory

p2m_open "LanglandsTunnell.Converse.ArchR"

theorem zetaIntegrand_one_zero (P : RealArchParam) (D : ArchDatumR P) (b : ZMod 2) (s : ℂ) (y : ℝ) :
    zetaIntegrand D.W 1 0 b s y
      = D.W (diagOne y) * (if b = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) *
          ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ := by
  simp [zetaIntegrand, quasiChar]

theorem integrand_pos (P : RealArchParam) (D : ArchDatumR P) (b : ZMod 2) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    zetaIntegrand D.W 1 0 b s t = ((t : ℂ) ^ (s - 1)) * (D.W (diagOne t) / (t : ℂ)) := by
  rw [zetaIntegrand_one_zero]
  have hs : ((SignType.sign t : ℝ) : ℂ) = 1 := by simp [sign_pos ht]
  rw [abs_of_pos ht]
  by_cases hb : b = 0
  · simp [hb, div_eq_mul_inv]; ring
  · simp [hb, hs, div_eq_mul_inv]; ring

theorem integrand_neg (P : RealArchParam) (D : ArchDatumR P) (b : ZMod 2) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    zetaIntegrand D.W 1 0 b s (-t) = ((t : ℂ) ^ (s - 1)) * ((-1 : ℂ) ^ b.val * D.W (diagOne (-t)) / (t : ℂ)) := by
  rw [zetaIntegrand_one_zero]
  have hs : ((SignType.sign (-t) : ℝ) : ℂ) = -1 := by simp [sign_neg (neg_lt_zero.mpr ht)]
  rw [abs_neg, abs_of_pos ht]
  by_cases hb : b = 0
  · simp [hb, div_eq_mul_inv]; ring
  · have hb1 : b.val = 1 := by
      have : b = 1 := by
        have h2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
        exact h2 b hb
      subst this; rfl
    simp [hb, hs, hb1, div_eq_mul_inv]; ring

theorem mellinConvergent_and_mellin_torus_eq_archFactor_mul_zetaEntire
    (P : RealArchParam) (D : ArchDatumR P) (b : ZMod 2) (s : ℂ) (hs : D.zeta_abscissa < s.re) :
    MellinConvergent (fun t : ℝ => (D.W (diagOne t) + (-1 : ℂ) ^ b.val * D.W (diagOne (-t))) / (t : ℂ)) s ∧
    mellin (fun t : ℝ => (D.W (diagOne t) + (-1 : ℂ) ^ b.val * D.W (diagOne (-t))) / (t : ℂ)) s
      = (P.twist 0 b).archFactor s * D.zetaEntire 1 0 b s := by
  have hdet : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by simp
  have hs' : D.zeta_abscissa < s.re + (0 : ℂ).re := by simpa using hs
  have hint : Integrable (zetaIntegrand D.W 1 0 b s) := D.zeta_integrable 1 0 b s hdet hs'
  have heq : ∫ y : ℝ, zetaIntegrand D.W 1 0 b s y = (P.twist 0 b).archFactor s * D.zetaEntire 1 0 b s :=
    D.zeta_eq 1 0 b s hdet hs'

  set F : ℝ → ℂ := zetaIntegrand D.W 1 0 b s with hF
  have hpos : IntegrableOn F (Set.Ioi 0) := hint.integrableOn
  have hneg : IntegrableOn F (Set.Iio 0) := hint.integrableOn

  have hneg' : IntegrableOn (fun t => F (-t)) (Set.Ioi 0) := by
    have := hneg.comp_neg
    simpa using this
  have hrefl : ∫ t in Set.Iio (0:ℝ), F t = ∫ t in Set.Ioi (0:ℝ), F (-t) := by
    rw [integral_comp_neg_Ioi, neg_zero, integral_Iic_eq_integral_Iio]
  have hsplit : (∫ t in Set.Ioi (0:ℝ), F t) + ∫ t in Set.Iio (0:ℝ), F t
      = (P.twist 0 b).archFactor s * D.zetaEntire 1 0 b s := by
    have h := integral_add_compl (μ := volume) (measurableSet_Ioi (a := (0:ℝ))) hint
    rw [Set.compl_Ioi, integral_Iic_eq_integral_Iio] at h
    rw [h, heq]

  set f : ℝ → ℂ := fun t => (D.W (diagOne t) + (-1 : ℂ) ^ b.val * D.W (diagOne (-t))) / (t : ℂ) with hf
  have hptw : ∀ t ∈ Set.Ioi (0:ℝ), (t : ℂ) ^ (s - 1) • f t = F t + F (-t) := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    rw [hF, integrand_pos P D b s ht, integrand_neg P D b s ht, hf, smul_eq_mul]
    ring
  have hconv : MellinConvergent f s := by
    unfold MellinConvergent
    have : IntegrableOn (fun t => F t + F (-t)) (Set.Ioi 0) := hpos.add hneg'
    exact this.congr_fun (fun t ht => (hptw t ht).symm) measurableSet_Ioi
  refine ⟨hconv, ?_⟩
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi hptw, integral_add hpos hneg', ← hrefl]
  exact hsplit

end Ws47.AD5

namespace Ws47
namespace PIN
namespace CB

theorem isIsotypicCuspFormAt_mono_S (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) {S S' : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (hSS' : S ⊆ S') (Ψ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Ψ φ) : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S' Ψ φ := by
  exact { smoothCusp := hφ.smoothCusp, continuous := hφ.continuous, level_invariant := hφ.level_invariant,
          hecke_eigen := fun v hv => hφ.hecke_eigen v (fun h => hv (hSS' h)),
          central_eigen := fun v hv => hφ.central_eigen v (fun h => hv (hSS' h)) }

theorem caseB_v3
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0)
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (hP : P = RealArchParam.principal u₁ a₁ u₂ a₂) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) :
    ∃ (Φ' : HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))),
      Φ'.AgreesAwayFromFinite Φ ∧
      IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ‖(Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b p‖ = 1) ∧
      (∃ R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral,
      Continuous R.toFun ∧
      ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      R.exceptionalSet ⊆ S ∧
      C 1 1 ≠ 0 ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ)) ∧
      ∀ par : InfinitePlace ℚ → ZMod 2,
        ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
          IsIsotypicCuspFormAt ℚ
              (productionPinsGeneral ℚ)
              R.centralChar (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).level S (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) φ ∧
          φ ≠ 0 ∧

          (∀ p : HeightOneSpectrum (𝓞 ℚ),
            ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
                W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                  fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
            (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
              ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ,
                  (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                    W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
            (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) ∧
          (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
            HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₂ →
              (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            P = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
          (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
              whittakerCoefficient ℚ
                  (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
                = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                    * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
              ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                    = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                        * (P.twist 0 a₁).archFactor s) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
            (b = par w ∨ b = par w + P.centralSign) →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                    = (P.twist 0 b).archFactor s)) := by
  classical
  have hψ : IsGlobalAddChar ℚ NumberField.StandardAddChar.psiQ := NumberField.StandardAddChar.isGlobalAddChar_psiQ

  obtain ⟨Θ, S, hΘΦ, R₁, hR₁c, hS, hcen, x₀, V, z₁, hx₀iso', hx0, hconvx, hwtall, hpair, hfibx', hV,
      hx₀V, hVloc, htorus⟩ :=
    LanglandsTunnell.exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_weightOne_whittakerCoefficient_torus_eq_archW_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_ne_of_ne
      c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0 u₁ u₂ a₁ a₂ hP ha hu
  subst hP
  have h0 : a₁ + a₂ ≠ 0 := by
    intro h; apply ha
    have : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
    exact this _ _ h
  have hWT1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 1 r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro w hw r x; have := hWT w hw r x; simpa [h0] using this

  obtain ⟨lam, -, hvec⟩ :=
    AutomorphicForm.exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num)
      (AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat) _ Rat.infinitePlace Rat.isReal_infinitePlace
  have hx₀wt : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map
      (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) x₀ :=
    hwtall Rat.infinitePlace Rat.isReal_infinitePlace
  obtain ⟨tys, hcut⟩ := exists_archTypeFamily_mem_one x₀ hx₀wt
  obtain ⟨hxs, hxd1, -, -⟩ := hvec _ (AutomorphicForm.TranslateSpanOccurrence.agrees_refl _) R₁ hR₁c S tys x₀ hx0
    (mem_isotypicCuspSubmodule' _ _ _ _ x₀ hx₀iso') hcut

  obtain ⟨S₁, hS₁⟩ := Ws47.PIN.exists_finset_norm_twist_b_eq_one c u d₁ d₂ T hc hd₁ hd hcov Φ _ archC dR dC
    hWF hWT hDE hnv hgen htype hP0 Θ hΘΦ
  have hSexc : R₁.exceptionalSet ⊆ S₁ ∪ S := hS.trans Finset.subset_union_right

  obtain ⟨κ, hκ, hT⟩ := device_on_fibre u₁ u₂ a₁ a₂ ha hu (hgen u₁ u₂ a₁ a₂ rfl) (htype u₁ u₂ a₁ a₂ rfl) archC dR dC
    (hWT1 _ _) (hDE _ _) NumberField.StandardAddChar.psiQ hψ.continuous x₀ hxs (show IsKfSmooth ℚ x₀ from hx₀iso'.smoothCusp.2) hx₀iso'.continuous hxd1 1 z₁ hfibx'
  have hκ0 : κ ≠ 0 := by rintro rfl; simp at hκ
  have hc₀ : κ⁻¹ * κ⁻¹ = 1 - 4 * (RealArchParam.principal u₁ a₁ u₂ a₂).laplaceEigenvalue := by
    rw [laplaceEigenvalue_principal]
    have h' : (u₁ - u₂) ^ 2 = (κ ^ 2)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv₀ (pow_ne_zero 2 hκ0)]
      linear_combination hκ
    rw [show κ⁻¹ * κ⁻¹ = (κ ^ 2)⁻¹ by rw [← inv_pow, sq], ← h']
    ring

  obtain ⟨archR', hdisj, -, -, -, C, hC11, hblock⟩ :=
    LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne_of_torus_profile_eigen
      _ R₁ hR₁c (S₁ ∪ S) (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂) hSexc (fun _ _ => htype) hcen x₀ (fun _ => 1)
      (isIsotypicCuspFormAt_mono_S _ _ Finset.subset_union_right _ x₀ hx₀iso') hx0 hconvx hwtall
      (by intro w hw v₁ v₂ b₁ b₂ h; cases h; exact ⟨Or.inr rfl, by
        have : ∀ x y : ZMod 2, x ≠ y → (1 : ZMod 2) = x + y := by decide
        exact_mod_cast this _ _ ha⟩)
      (by intro w hw u₀ n hn h; cases h)
      hpair (fun _ _ => ⟨u₁, u₂, a₁, a₂, rfl, ha, hu⟩)
      (fun _ _ => κ⁻¹) (fun w hw => hc₀)
      (by intro w hw g hg; obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _; exact hT g hg)
      V hV hx₀V hVloc htorus

  have hP' : archR' Rat.infinitePlace Rat.isReal_infinitePlace = RealArchParam.principal u₁ a₁ u₂ a₂ := by
    obtain ⟨φ, Wr, k, -, -, -, -, -, ⟨ρ', hρ', hWr⟩, -, -, -, -, -, -, hmel⟩ := hblock (fun _ => 0)
    obtain ⟨s₀, hs₀⟩ := hmel Rat.infinitePlace Rat.isReal_infinitePlace 0 (Or.inl rfl)
    have hprof := fibre_profile_eq_datum _ archC dR dC NumberField.StandardAddChar.psiQ x₀ 1 (Subgroup.one_mem _) z₁ hfibx' Wr ρ'
      (fun w a ha => by rw [mul_one]; exact hWr w a ha)
    have hP'dj : archR' Rat.infinitePlace Rat.isReal_infinitePlace = RealArchParam.principal u₁ a₁ u₂ a₂ ∨
        archR' Rat.infinitePlace Rat.isReal_infinitePlace = RealArchParam.principal u₁ a₂ u₂ a₁ := by
      rcases hdisj Rat.infinitePlace Rat.isReal_infinitePlace with h | ⟨v₁, v₂, b₁, b₂, h1, h2⟩
      · exact Or.inl h
      · cases h1; exact Or.inr h2
    set D := dR Rat.infinitePlace Rat.isReal_infinitePlace with hDdef
    refine LanglandsTunnell.RealArchParam.eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire u₁ u₂ a₁ a₂ ha hu
      (htype u₁ u₂ a₁ a₂ rfl) _ hP'dj 1 one_ne_zero (fun s => ρ' * z₁ * D.zetaEntire 1 0 0 s)
      ((D.zetaEntire_differentiable 1 0 0).const_mul _) (max s₀ D.zeta_abscissa) ?_
    intro s hs
    have h1 := (hs₀ s (lt_of_le_of_lt (le_max_left _ _) hs)).2
    have h2 := (Ws47.AD5.mellinConvergent_and_mellin_torus_eq_archFactor_mul_zetaEntire _ D 0 s
      (lt_of_le_of_lt (le_max_right _ _) hs)).2

    have hcongr : mellin (fun t : ℝ => (Wr Rat.infinitePlace t + (-1 : ℂ) ^ (0 : ZMod 2).val * Wr Rat.infinitePlace (-t)) / (t : ℂ)) s
        = (ρ' * z₁) * mellin (fun t : ℝ => (D.W (ArchR.diagOne t) + (-1 : ℂ) ^ (0 : ZMod 2).val * D.W (ArchR.diagOne (-t))) / (t : ℂ)) s := by
      rw [show (ρ' * z₁) * mellin (fun t : ℝ => (D.W (ArchR.diagOne t) + (-1 : ℂ) ^ (0 : ZMod 2).val * D.W (ArchR.diagOne (-t))) / (t : ℂ)) s
          = (ρ' * z₁) • mellin (fun t : ℝ => (D.W (ArchR.diagOne t) + (-1 : ℂ) ^ (0 : ZMod 2).val * D.W (ArchR.diagOne (-t))) / (t : ℂ)) s from rfl,
        ← mellin_const_smul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (t : ℝ) ≠ 0 := (Set.mem_Ioi.mp ht).ne'
      have hneg : Wr Rat.infinitePlace (-(t : ℂ)) = ρ' * z₁ * D.W (ArchR.diagOne (-t)) := by
        have := hprof (-t) (neg_ne_zero.mpr ht0); simpa [hDdef] using this
      simp only [smul_eq_mul, Pi.smul_apply, hprof t ht0, hneg, hDdef]
      ring
    rw [one_mul, ← h1, hcongr, h2]
    ring
  have harch : archR' = fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₂ := by
    funext w hw; obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _; exact hP'
  subst harch

  refine ⟨Θ, S₁ ∪ S, hΘΦ, ⟨R₁, hR₁c⟩, ?_, R₁, hR₁c, C, hSexc, hC11, fun _ _ => htype, fun _ _ => hgen, hcen, ?_⟩
  · intro p hp; exact hS₁ p (fun h => hp (Finset.mem_union_left _ h))
  · intro par
    obtain ⟨φ, Wr, k, h1, h2, hL, h3, h4, -, h5, h6, h7, h8, h9, h10, h11⟩ := hblock par
    exact ⟨φ, Wr, k, h1, h2, hL, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Ws47.PIN.CB

open Ws47.PIN in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ∃ (Φ' : HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))),
      Φ'.AgreesAwayFromFinite Φ ∧
      IsArithGenuineCuspRealizable ℚ (productionPinsGeneral ℚ) (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ‖(Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b p‖ = 1) ∧
      (∃ R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral,
      Continuous R.toFun ∧
      ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      R.exceptionalSet ⊆ S ∧
      C 1 1 ≠ 0 ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ)) ∧
      ∀ par : InfinitePlace ℚ → ZMod 2,
        ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
          IsIsotypicCuspFormAt ℚ
              (productionPinsGeneral ℚ)
              R.centralChar (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).level S (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) φ ∧
          φ ≠ 0 ∧

          (∀ p : HeightOneSpectrum (𝓞 ℚ),
            ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
                W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                  fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
            (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
              ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ,
                  (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                    W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
            (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ p φ,
              ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) ∧
          (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
            HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₂ →
              (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            P = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
          (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
              whittakerCoefficient ℚ
                  (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
                = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                    * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
              ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            P = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                    = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                        * (P.twist 0 a₁).archFactor s) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
            (b = par w ∨ b = par w + P.centralSign) →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                    = (P.twist 0 b).archFactor s)) := by
  classical
  by_cases hB : ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂ ∧ u₁ ≠ u₂
  · obtain ⟨u₁, u₂, a₁, a₂, hP, ha, hu⟩ := hB
    exact Ws47.PIN.CB.caseB_v3 c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0 u₁ u₂ a₁ a₂ hP ha hu
  have hcase : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = a₂ ∨ u₁ = u₂ := by
    intro u₁ u₂ a₁ a₂ hP
    by_contra h
    push_neg at h
    exact hB ⟨u₁, u₂, a₁, a₂, hP, h.1, h.2⟩

  obtain ⟨Θ, S, hΘΦ, R, hRc, hS, hcen, φ₁, k₁, V, hiso, hne, hconv, hwt, hminp, hmind, hpair, hJ, hlow, hlow1, hV, hφ₁V,
      hVloc, htorus⟩ :=
    LanglandsTunnell.exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
      c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0

  obtain ⟨S₁, hS₁⟩ := exists_finset_norm_twist_b_eq_one c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0 Θ hΘΦ
  have hSexc : R.exceptionalSet ⊆ S₁ ∪ S := hS.trans Finset.subset_union_right

  obtain ⟨C, hC11, hC⟩ :=
    LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_minimalWeight
      _ R hRc (S₁ ∪ S) (fun _ _ => P) hSexc (fun _ _ => htype) hcen φ₁ k₁
      (Ws47.PIN.CB.isIsotypicCuspFormAt_mono_S _ _ Finset.subset_union_right _ φ₁ hiso) hne hconv hwt hminp hmind hpair
      hJ hlow hlow1 (fun _ _ => hcase) V hV hφ₁V hVloc htorus
  refine ⟨Θ, S₁ ∪ S, hΘΦ, ⟨R, hRc⟩, ?_, R, hRc, C, hSexc, hC11, fun _ _ => htype, fun _ _ => hgen, hcen, hC⟩
  intro p hp
  exact hS₁ p (fun h => hp (Finset.mem_union_left _ h))

end S_LanglandsTunnell_exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_isArithGenuineCuspRealizable_twist_whittaker_link_localSpaceAt_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen (solution)
