-- Prove2me | solution 1 for ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9c9bc61b-6306-5d77-8336-34220ff289c5

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_x1x0_gamma0
import Theorems.Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ)
      (F : Fin n → ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      D ≠ 0 ∧
      (∀ i, c i ∈ IntermediateField.adjoin ℚ
        ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ)) ∧
      (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧
      ((D : ℂ) • fun τ : UpperHalfPlane =>
          ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))
        = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ) := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩

  have hle0 : CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p := by
    intro A hA
    obtain ⟨h00, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem _ _).mp hA
    have castM := ZMod.castHom (dvd_mul_right M p) (ZMod M)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩
      · simpa using congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h00
      · simpa using congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h11
      · simpa using congrArg (ZMod.castHom (dvd_mul_right M p) (ZMod M)) h10
    · rw [CongruenceSubgroup.Gamma0_mem]
      simpa using congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) h10
  have hle : ((CongruenceSubgroup.Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono hle0
  obtain ⟨F, hF⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_x1x0_gamma0 p M hpM f γ hγ hγp
  have hf' : ModularCurve.IsIntegralQExp (ModularCurve.restrictForm hle f) p₀ := hf
  have hcoeff : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈
      IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by
    intro n
    rw [hF]
    have h := ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul p M hpM
      (ModularCurve.restrictForm hle f) hf' γ hγ hγp n
    rwa [ModularCurve.coe_restrictForm] at h
  obtain ⟨n, c, G, r, hc, hG, hsum⟩ :=
    ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0 p M hpM _ F hcoeff
  refine ⟨1, n, c, G, r, one_ne_zero, hc, hG, ?_⟩
  rw [Int.cast_one, one_smul, ← hF, hsum]

end S_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0
end P2MW
export P2MW.S_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0 (solution)
