-- Prove2me | solution 1 for ModularCurve.qExpansion_slash_coeff_mem_range_of_isIntegralQExp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/83ef1b31-bdf6-5ba3-bfaa-e40d4aa420fe

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansion_slash_coeff_mem_range_of_isIntegralQExp
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace Ws50Slash

theorem mem_range_of_isAlgebraic (ι : AlgebraicClosure ℚ →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) :
    z ∈ Set.range ι := by
  have hz' : IsIntegral ℚ z := hz.isIntegral
  set P : Polynomial ℚ := minpoly ℚ z with hP
  have hP0 : P ≠ 0 := minpoly.ne_zero hz'
  have hcomp : ι.comp (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ ℂ := Subsingleton.elim _ _
  have hmap : P.map (algebraMap ℚ ℂ) = (P.map (algebraMap ℚ (AlgebraicClosure ℚ))).map ι := by
    rw [Polynomial.map_map, hcomp]
  have hroot : ((P.map (algebraMap ℚ (AlgebraicClosure ℚ))).map ι).IsRoot z := by
    rw [← hmap, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def, hP, minpoly.aeval]
  have hne : (P.map (algebraMap ℚ (AlgebraicClosure ℚ))).map ι ≠ 0 := by
    rw [← hmap]; exact Polynomial.map_ne_zero hP0
  have hmem : z ∈ ((P.map (algebraMap ℚ (AlgebraicClosure ℚ))).map ι).roots :=
    (Polynomial.mem_roots hne).mpr hroot
  rw [(IsAlgClosed.splits _).roots_map ι] at hmem
  obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hmem
  exact ⟨w, rfl⟩

end Ws50Slash

theorem solution
    (L : ℕ) [NeZero L] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 L : Subgroup (GL (Fin 2) ℝ)) k)
    {r : PowerSeries ℤ} (hF : ModularCurve.IsIntegralQExp F r)
    (ι : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) (n : ℕ) :
    (UpperHalfPlane.qExpansion L ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n ∈ Set.range ι := by
  obtain ⟨a, ha⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff L F hF γ
  set c : ℂ := (UpperHalfPlane.qExpansion L ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n with hc
  have hL : ((L : ℂ)) ^ a ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)

  have h1 : IsAlgebraic ℚ ((L : ℂ) ^ a * c) :=
    ((ha n).isAlgebraic).extendScalars (algebraMap ℤ ℚ).injective_int

  have h2 : IsAlgebraic ℚ (algebraMap ℚ ℂ (((L : ℚ) ^ a)⁻¹) * ((L : ℂ) ^ a * c)) :=
    (isAlgebraic_algebraMap _).mul h1
  have h3 : algebraMap ℚ ℂ (((L : ℚ) ^ a)⁻¹) * ((L : ℂ) ^ a * c) = c := by
    rw [map_inv₀, map_pow]
    simp only [eq_ratCast, Rat.cast_natCast]
    field_simp
  rw [h3] at h2
  exact Ws50Slash.mem_range_of_isAlgebraic ι h2

end S_ModularCurve_qExpansion_slash_coeff_mem_range_of_isIntegralQExp
end P2MW
export P2MW.S_ModularCurve_qExpansion_slash_coeff_mem_range_of_isIntegralQExp (solution)
