-- Prove2me | solution 1 for ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/58995cf6-8fd4-5aaa-90a5-808e3422a0c5

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Theorems.Thm_UpperHalfPlane_qExpansion_coeff_nat_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open UpperHalfPlane in
open scoped MatrixGroups ModularForm Manifold in
set_option maxHeartbeats 3200000 in
theorem solution (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (a : ℕ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
      (p₁ : PowerSeries ℤ), ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ a) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by
  classical
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h1per : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1

  obtain ⟨D, f₁', p₁', hD, hp₁', hf₁'⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M f hp γ hγ
  have hDC : (D : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hD

  set g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k := ((D : ℂ)⁻¹) • f₁' with hgdef
  have hg : (⇑g : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by
    rw [hgdef, ModularForm.IsGLPos.coe_smul, hf₁', smul_smul, inv_mul_cancel₀ hDC, one_smul]
  have hqg : ∀ n : ℕ, (qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff n =
      ((D : ℂ)⁻¹) * ((PowerSeries.coeff n p₁' : ℤ) : ℂ) := by
    intro n
    rw [hgdef, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1per, map_smul,
      smul_eq_mul, ← hp₁'.coeff n]

  have hper : Function.Periodic ((⇑g : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex g h1per
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1per⟩
  have hbdd : IsBoundedAtImInfty (⇑g : UpperHalfPlane → ℂ) := ModularFormClass.bdd_at_infty g
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑g : UpperHalfPlane → ℂ) := ModularFormClass.holo g
  have hPC : ∀ n : ℕ, (qExpansion (M : ℝ) ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ)).coeff (M * n) =
      (qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff n := by
    intro n
    have h := UpperHalfPlane.qExpansion_coeff_nat_mul one_pos hper hhol hbdd hMpos (M * n)
    rw [mul_one, if_pos (dvd_mul_right M n), Nat.mul_div_cancel_left n hMpos] at h
    rw [← hg]
    exact h

  obtain ⟨a, ha⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_coeff M f hp γ

  set r : ℕ → ℚ := fun n => (M : ℚ) ^ a * ((D : ℚ)⁻¹ * ((PowerSeries.coeff n p₁' : ℤ) : ℚ)) with hrdef
  have hrC : ∀ n : ℕ, algebraMap ℚ ℂ (r n) = (M : ℂ) ^ a * (qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff n := by
    intro n
    rw [hqg n, hrdef]
    simp only [eq_ratCast]
    push_cast
    ring
  have hrint : ∀ n : ℕ, IsIntegral ℤ (r n) := by
    intro n
    have h := ha (M * n)
    rw [hPC n, ← hrC n] at h
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp h
  have hrZ : ∀ n : ℕ, ∃ m : ℤ, (m : ℚ) = r n := by
    intro n
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hrint n)
    exact ⟨y, by simpa using hy⟩
  choose m hm using hrZ

  refine ⟨a, ((M : ℂ) ^ a) • g, PowerSeries.mk m, ?_, ?_⟩
  · unfold ModularCurve.IsIntegralQExp
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1per]
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_smul, smul_eq_mul, eq_intCast, ← hrC n,
      ← hm n, eq_ratCast, Rat.cast_intCast]
  · rw [ModularForm.IsGLPos.coe_smul, hg]

end S_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
end P2MW
export P2MW.S_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 (solution)
