-- Prove2me | solution 1 for ModularCurve.coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9863b03d-6c61-5121-a783-fb9b48d58681

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_frobeniusInputsModL
import Theorems.Thm_ModularCurve_frobeniusModL_norm_eq_pow
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
import Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve AlgebraicCurve

set_option maxHeartbeats 6400000 in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p] (N : ℕ) [NeZero N]
    (δ : Pic0.torsion K (modularFunctionFieldFullC K N) p →+ Ω[↥(modularFunctionFieldFullC K N)⁄K])
    (hδ : ∀ (y : Pic0.torsion K (modularFunctionFieldFullC K N) p)
        (E : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) (g : modularFunctionFieldFullC K N),
        Pic0.mk E = (y : Pic0 K (modularFunctionFieldFullC K N)) → g ≠ 0 →
        (∀ v : Place K (modularFunctionFieldFullC K N),
          (p : ℤ) * (E : Divisor K (modularFunctionFieldFullC K N)) v = v.ord g) →
        δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) g)
    (x y : Pic0.torsion K (modularFunctionFieldFullC K N) p)
    (hy : (y : Pic0 K (modularFunctionFieldFullC K N)) =
      frobeniusPushforwardModL K N p (x : Pic0 K (modularFunctionFieldFullC K N))) (n : ℤ) :
    (qExpansionDiffAlong (modularFunctionFieldFullC K N).val (δ y)).coeff n =
      ((qExpansionDiffAlong (modularFunctionFieldFullC K N).val (δ x)).coeff n) ^ p := by
  obtain ⟨hP, hfin, hFI, hNF⟩ := frobeniusInputsModL K N (ℓ := p)
  haveI := hP
  obtain ⟨D, f, hDx, hf0, -, hord⟩ :=
    Pic0.exists_mk_eq_and_dvd_ord_of_mem_torsion (x := (x : Pic0 K (modularFunctionFieldFullC K N))) x.2
  have hD : ∀ v : Place K (modularFunctionFieldFullC K N),
      (p : ℤ) * (D : Divisor K (modularFunctionFieldFullC K N)) v = v.ord f := fun v => (hord v).symm

  let g : modularFunctionFieldFullC K N :=
    (letI := AlgebraicCurve.algebraAlong (frobeniusModL K N p)
     Algebra.norm (↥(modularFunctionFieldFullC K N)) f)
  have hFg : frobeniusModL K N p g = f ^ p := frobeniusModL_norm_eq_pow K N hfin f
  have hg0 : g ≠ 0 := by
    intro h0
    apply pow_ne_zero p hf0
    rw [← hFg, h0, map_zero]

  have hpD : ∀ w : Place K (modularFunctionFieldFullC K N),
      ((p : ℤ) • (D : Divisor K (modularFunctionFieldFullC K N))) w = w.ord f := fun w => by
    rw [Finsupp.smul_apply, smul_eq_mul, hD w]
  have hNFv : ∀ v : Place K (modularFunctionFieldFullC K N),
      frobeniusDivPushforwardModL K N p ((p : ℤ) • (D : Divisor K (modularFunctionFieldFullC K N))) v
        = v.ord g := by
    intro v
    exact hNF f hf0 _ hpD v
  have hFrD : ∀ v : Place K (modularFunctionFieldFullC K N),
      (p : ℤ) * ((frobeniusDegZeroPushforwardModL K N p D :
        Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
          Divisor K (modularFunctionFieldFullC K N)) v = v.ord g := by
    intro v
    rw [coe_frobeniusDegZeroPushforwardModL, ← hNFv v, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
  have hy' : Pic0.mk (frobeniusDegZeroPushforwardModL K N p D) =
      (y : Pic0 K (modularFunctionFieldFullC K N)) := by
    rw [hy, ← hDx, frobeniusPushforwardModL_mk hfin hFI hNF]
  have h1 : δ y = g⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) g := hδ y _ g hy' hg0 hFrD
  have h2 : δ x = f⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) f := hδ x D f hDx hf0 hD
  rw [h1, h2]
  exact coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow K N f g hFg n

end S_ModularCurve_coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL
end P2MW
export P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_apply_of_coe_eq_frobeniusPushforwardModL (solution)
