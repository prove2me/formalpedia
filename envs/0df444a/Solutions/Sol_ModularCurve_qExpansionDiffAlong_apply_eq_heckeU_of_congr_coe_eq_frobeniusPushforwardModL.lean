-- Prove2me | solution 1 for ModularCurve.qExpansionDiffAlong_apply_eq_heckeU_of_congr_coe_eq_frobeniusPushforwardModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/b27d1840-8177-5bb5-9a9d-51830a2ef903

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_LaurentSeries_HeckeU
import Theorems.Thm_ModularCurve_exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansionDiffAlong_apply_eq_heckeU_of_congr_coe_eq_frobeniusPushforwardModL
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve AlgebraicCurve

set_option maxHeartbeats 6400000 in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] [IsCurveOver K (modularFunctionFieldC K N)]
    (hE : modularFunctionFieldC K N = modularFunctionFieldFullC K N)
    (C : Ω[↥(modularFunctionFieldC K N)⁄K] →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hsemi : ∀ (f : modularFunctionFieldC K N) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]),
      C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : modularFunctionFieldC K N,
      C (KaehlerDifferential.D K (modularFunctionFieldC K N) f) = 0)
    (hlog : ∀ f : modularFunctionFieldC K N,
      C (f ^ (p - 1) • KaehlerDifferential.D K (modularFunctionFieldC K N) f)
        = KaehlerDifferential.D K (modularFunctionFieldC K N) f)
    (δ : Pic0.torsion K (modularFunctionFieldC K N) p →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hδ : ∀ (y : Pic0.torsion K (modularFunctionFieldC K N) p)
        (E : Divisor.degZero (K := K) (F := modularFunctionFieldC K N)) (g : modularFunctionFieldC K N),
        Pic0.mk E = (y : Pic0 K (modularFunctionFieldC K N)) → g ≠ 0 →
        (∀ v : Place K (modularFunctionFieldC K N),
          (p : ℤ) * (E : Divisor K (modularFunctionFieldC K N)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldC K N) g)
    (x y : Pic0.torsion K (modularFunctionFieldC K N) p)
    (hy : Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
            (fun a => (IntermediateField.equivOfEq hE).commutes a) (y : Pic0 K (modularFunctionFieldC K N)) =
          frobeniusPushforwardModL K N p
            (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
              (fun a => (IntermediateField.equivOfEq hE).commutes a) (x : Pic0 K (modularFunctionFieldC K N)))) :
    qExpansionDiffAlong (modularFunctionFieldC K N).val (δ y) =
      LaurentSeries.heckeU K p (Fact.out : p.Prime).pos
        (qExpansionDiffAlong (modularFunctionFieldC K N).val (δ x)) := by
  have hp : p.Prime := Fact.out
  haveI : PerfectField K := IsAlgClosed.perfectField K

  obtain ⟨τ, δ₂, hτ, hδ₂, hq⟩ :=
    exists_addMonoidHom_torsion_recipe_qExpansionDiffAlong_congr_eq K p hE δ hδ
  have hy₂ : ((τ y : Pic0.torsion K (modularFunctionFieldFullC K N) p) : Pic0 K (modularFunctionFieldFullC K N)) =
      frobeniusPushforwardModL K N p
        ((τ x : Pic0.torsion K (modularFunctionFieldFullC K N) p) : Pic0 K (modularFunctionFieldFullC K N)) := by
    rw [hτ, hτ]
    exact hy
  have hcoef : ∀ n : ℤ, (qExpansionDiffAlong (modularFunctionFieldC K N).val (δ y)).coeff n =
      ((qExpansionDiffAlong (modularFunctionFieldC K N).val (δ x)).coeff n) ^ p := by
    intro n
    have h := coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL K N δ₂ hδ₂ (τ x) (τ y) hy₂ n
    rwa [hq, hq] at h

  have hfix : C (δ x) = δ x := by
    obtain ⟨D, f, hDx, hf0, -, hord⟩ :=
      Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion (x := (x : Pic0 K (modularFunctionFieldC K N))) x.2
    have hx : δ x = f⁻¹ • KaehlerDifferential.D K (modularFunctionFieldC K N) f :=
      hδ x D f hDx hf0 (fun v => (hord v).symm)
    rw [hx]
    have key : f⁻¹ • KaehlerDifferential.D K (modularFunctionFieldC K N) f =
        (f⁻¹) ^ p • (f ^ (p - 1) • KaehlerDifferential.D K (modularFunctionFieldC K N) f) := by
      rw [smul_smul]
      congr 1
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
      calc f⁻¹ = f⁻¹ * (f⁻¹ * f) ^ (p - 1) := by rw [inv_mul_cancel₀ hf0, one_pow, mul_one]
        _ = (f⁻¹) ^ p * f ^ (p - 1) := by rw [mul_pow, ← mul_assoc, ← pow_succ', hp1]
    conv_lhs => rw [key]
    rw [hsemi, hlog]

  ext n
  rw [LaurentSeries.coeff_heckeU, hcoef n, ← hfix, coeff_qExpansionDiffAlong_cartier_pow K p N C hsemi hker hlog,
    hfix, mul_comm]

end S_ModularCurve_qExpansionDiffAlong_apply_eq_heckeU_of_congr_coe_eq_frobeniusPushforwardModL
end P2MW
export P2MW.S_ModularCurve_qExpansionDiffAlong_apply_eq_heckeU_of_congr_coe_eq_frobeniusPushforwardModL (solution)
