-- Prove2me | solution 1 for ModularCurve.XOneP.exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5d0c0cc0-3096-5d4a-877e-2324159b1861

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq
import Theorems.Thm_ModularCurve_XOneP_exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq
import Theorems.Thm_ModularCurve_XOneP_coe_apply_coeffEmb_eq_coeffEmb_atkinLehnerInvolutionFull_of_atkinLehnerSlash_p
import Theorems.Thm_ModularCurve_XOneP_coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open scoped MatrixGroups ModularForm

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M) [NeZero p]

    (hβdef : ModularCurve.HeckeBetaOneDefined (M * p) p) :
    ∃ d d' : ℕ, d.Coprime (M * p) ∧ d'.Coprime (M * p) ∧
      ∃ (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))),

        (∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
          (hf : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ ModularCurve.x1FunctionFieldBar (M * p)),
          ((τ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), hf⟩ : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((ModularCurve.atkinLehnerInvolutionFull M p f :
              ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)) ∧

        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)),
          W (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p x) =
            ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p
              (ModularCurve.diamondAutBar (M * p) d (τ x))) ∧

        (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)),
          W (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) (M * p) p x) =
            ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) (M * p) p
              (ModularCurve.diamondAutBar (M * p) d' (τ x))) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

  let ι : AlgebraicClosure ℚ →+* ℂ := ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : AlgebraicClosure ℚ →+* ℂ)

  have hcop : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u₂, v₂, huv₂⟩ := Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left 2 hcop)
  have hrel : (p : ℤ) * u - (M : ℤ) * (-v) = 1 := by linear_combination huv
  have hrel₂ : (p : ℤ) ^ 2 * u₂ - (M : ℤ) * (-v₂) = 1 := by
    push_cast at huv₂
    linear_combination huv₂
  let γ : SL(2, ℤ) := ⟨!![1, -v; (M : ℤ), (p : ℤ) * u], by rw [Matrix.det_fin_two_of]; linear_combination hrel⟩
  let γ' : SL(2, ℤ) := ⟨!![u, -(-v); -(M : ℤ), (p : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination hrel⟩
  let δ : SL(2, ℤ) := ⟨!![1, -v₂; (M : ℤ), (p : ℤ) ^ 2 * u₂], by rw [Matrix.det_fin_two_of]; linear_combination hrel₂⟩
  let δ' : SL(2, ℤ) := ⟨!![u₂, -(-v₂); -(M : ℤ), (p : ℤ) ^ 2], by rw [Matrix.det_fin_two_of]; linear_combination hrel₂⟩

  obtain ⟨τ, hτ⟩ := ModularCurve.XOneP.exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p p M hpM (-v) u hrel γ γ' rfl rfl ι
  obtain ⟨W, hW⟩ := ModularCurve.XOneP.exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq p M hpM (-v₂) u₂ hrel₂ δ δ' rfl rfl ι

  obtain ⟨d, d', hd, hd', hL1, hL2⟩ :=
    ModularCurve.XOneP.exists_coprime_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_of_atkinLehnerSlash_p_of_atkinLehnerSlash_sq p M hpM hM hβdef ι (-v) u hrel γ γ' rfl rfl (-v₂) u₂ hrel₂ δ δ' rfl rfl τ hτ W hW
  have hplus := ModularCurve.XOneP.coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p p M hpM (-v) u hrel γ rfl ι τ hτ.2.1 hτ.2.2.2
  have hAL := ModularCurve.XOneP.coe_apply_coeffEmb_eq_coeffEmb_atkinLehnerInvolutionFull_of_atkinLehnerSlash_p p M hpM hM τ hplus
  exact ⟨d, d', hd, hd', τ, W, hAL, hL1, hL2⟩

end S_ModularCurve_XOneP_exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull (solution)
