-- Prove2me | solution 1 for ModularForm.qExpansion_E4_mul_theta_discriminant_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/58601e44-c349-582e-b387-00c9a3c2488a

import Mathlib
import Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_qExpansion_E4_mul_theta_discriminant_sub
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open UpperHalfPlane ModularForm EisensteinSeries CongruenceSubgroup
open scoped MatrixGroups Manifold

noncomputable section

theorem solution :
    qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ) *
        PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 ModularForm.discriminant).coeff n)
      - 3 * PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff n)
        * qExpansion 1 ModularForm.discriminant
      = qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ) * qExpansion 1 ModularForm.discriminant := by

  have hΓ : ((Gamma 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := Gamma_one_coe_eq_SL
  have h1 : (1 : ℝ) ∈ ((Gamma 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [hΓ]; exact one_mem_strictPeriods_SL
  obtain ⟨B, -, hBq⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq h1
    (E₄.mcast rfl hΓ) ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).mcast rfl hΓ)

  set P4 : PowerSeries ℂ := qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ) with hP4
  set P6 : PowerSeries ℂ := qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ) with hP6
  set PD : PowerSeries ℂ := qExpansion 1 ModularForm.discriminant with hPD
  change qExpansion 1 (B : ℍ → ℂ) =
      PowerSeries.C ((4 : ℤ) : ℂ) * P4 * PowerSeries.mk (fun n : ℕ => (n : ℂ) * PD.coeff n)
        - PowerSeries.C ((12 : ℤ) : ℂ) * PowerSeries.mk (fun n : ℕ => (n : ℂ) * P4.coeff n) * PD at hBq

  have h40 : P4.coeff 0 = 1 := E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
  have h60 : P6.coeff 0 = 1 := E_qExpansion_coeff_zero (by norm_num) ⟨3, rfl⟩
  have hD0 : PD.coeff 0 = 0 := by
    rw [hPD, ← CuspForm.coe_discriminant, UpperHalfPlane.qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex _ one_mem_strictPeriods_SL)]
    exact (CuspFormClass.zero_at_infty CuspForm.discriminant).valueAtInfty_eq_zero
  have hD1 : PD.coeff 1 = 1 := discriminant_qExpansion_coeff_one

  set B' : ModularForm 𝒮ℒ 18 := B.mcast (by norm_num) hΓ.symm with hB'
  have hB'q : qExpansion 1 (B' : ℍ → ℂ) = qExpansion 1 (B : ℍ → ℂ) := rfl
  have hcusp : IsCuspForm B' := by
    rw [isCuspForm_iff_coeffZero_eq_zero, hB'q, hBq]
    simp [h40, hD0]
  obtain ⟨G, hG⟩ := hcusp
  have hGB : (G : ℍ → ℂ) = (B : ℍ → ℂ) := by
    funext τ
    have := DFunLike.congr_fun hG τ
    first | exact this | simpa [CuspForm.toModularFormₗ_apply] using this | simpa +zetaDelta [CuspForm.toModularFormₗ_apply] using this

  set M : ModularForm 𝒮ℒ 6 := (CuspForm.discriminantEquiv G).mcast (by norm_num) with hM
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • E₆ = M :=
    (finrank_eq_one_iff_of_nonzero' E₆ (E_ne_zero (by norm_num) ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_six_rank_one) M
  have hpt : (B : ℍ → ℂ) = ModularForm.discriminant * (c • (⇑ModularForm.E₆ : ℍ → ℂ)) := by
    rw [← hGB]
    funext τ
    have h2 : M τ = c * E₆ τ := by
      have := DFunLike.congr_fun hc τ
      rw [IsGLPos.smul_apply, smul_eq_mul] at this
      exact this.symm
    have h3 : ModularForm.discriminant τ * M τ = G τ := by
      change ModularForm.discriminant τ * (G τ / ModularForm.discriminant τ) = G τ
      exact mul_div_cancel₀ _ (discriminant_ne_zero τ)
    rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, ← h2, h3]
  have hq2 : qExpansion 1 (B : ℍ → ℂ) = PD * (c • P6) := by
    rw [hpt, UpperHalfPlane.qExpansion_mul, UpperHalfPlane.qExpansion_smul]
    · exact ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ one_pos
        one_mem_strictPeriods_SL
    · rw [← CuspForm.coe_discriminant]
      exact ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
        one_mem_strictPeriods_SL
    · have : (c • (⇑ModularForm.E₆ : ℍ → ℂ)) = ⇑(c • ModularForm.E₆) := by
        rw [IsGLPos.coe_smul]
      rw [this]
      exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL
  have key := hBq.symm.trans hq2

  have hc4 : c = 4 := by
    have := congrArg (PowerSeries.coeff 1) key
    simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, h40, h60, hD0, hD1] at this
    first
      | exact this.symm
      | exact this
      | (norm_num at this; first | exact this.symm | exact this)
  subst hc4

  have h4 : (PowerSeries.C (4 : ℂ)) ≠ 0 := by simp
  apply mul_left_cancel₀ h4
  have e12 : PowerSeries.C ((12 : ℤ) : ℂ) = PowerSeries.C (4 : ℂ) * 3 := by
    rw [show (3 : PowerSeries ℂ) = PowerSeries.C 3 from rfl, ← map_mul]; norm_num
  have e4 : PowerSeries.C ((4 : ℤ) : ℂ) = PowerSeries.C (4 : ℂ) := by norm_num
  rw [e12, e4, PowerSeries.smul_eq_C_mul] at key
  calc PowerSeries.C (4 : ℂ) * (P4 * PowerSeries.mk (fun n : ℕ => (n : ℂ) * PD.coeff n)
          - 3 * PowerSeries.mk (fun n : ℕ => (n : ℂ) * P4.coeff n) * PD)
        = PowerSeries.C (4 : ℂ) * P4 * PowerSeries.mk (fun n : ℕ => (n : ℂ) * PD.coeff n)
          - PowerSeries.C (4 : ℂ) * 3 * PowerSeries.mk (fun n : ℕ => (n : ℂ) * P4.coeff n) * PD := by
          ring
    _ = PD * (PowerSeries.C 4 * P6) := key
    _ = PowerSeries.C (4 : ℂ) * (P6 * PD) := by ring

end

end S_ModularForm_qExpansion_E4_mul_theta_discriminant_sub
end P2MW
export P2MW.S_ModularForm_qExpansion_E4_mul_theta_discriminant_sub (solution)
