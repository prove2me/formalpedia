-- Prove2me | solution 1 for ModularCurve.ofAlgAut_smul_ofAlgAut_smul_of_fricke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/064afb88-43a5-5b36-bfde-c779f4d4750d

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ofAlgAut_smul_ofAlgAut_smul_of_fricke
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ofAlgAut_smul_ofAlgAut_smul_of_fricke.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticRingAut arithmeticRingAut_algebraMap arithmeticGalois galois_smul_pic0_def modularFunctionFieldBar JZero qExpand qExpand_one_apply jq modularFunctionFieldFull jqd_mem_full coeffEmb coeffMap_coeffEmb coeffEmb_mem_laurentBaseChange adjoin_jBar_jNBar_eq_top jq_mem_full"
namespace PEdge
p2m_open "ModularCurve"

section Fricke

variable (N : ℕ) [NeZero N]

def IsFrickeBar (σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N) : Prop :=
  ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
    ∀ x : modularFunctionFieldBar N,
      (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
        ((σ x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
          = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq)

def jBarGen : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

def jNBarGen : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

theorem adjoin_gens_eq_top :
    IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBarGen N, jNBarGen N} : Set (modularFunctionFieldBar N))
      = ⊤ :=
  ModularCurve.adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N

variable {N}
variable {σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N}

theorem fricke_jBarGen (hσ : IsFrickeBar N σ) : σ (jBarGen N) = jNBarGen N := by
  refine Subtype.ext ?_
  refine hσ 1 N (one_mul N) (jBarGen N) ?_
  show coeffEmb (AlgebraicClosure ℚ) jq = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq)
  rw [qExpand_one_apply]

theorem fricke_jNBarGen (hσ : IsFrickeBar N σ) : σ (jNBarGen N) = jBarGen N := by
  refine Subtype.ext ?_
  have h := hσ N 1 (mul_one N) (jNBarGen N) rfl
  rw [qExpand_one_apply] at h
  exact h

theorem algHom_ext_gens {φ ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N}
    (h1 : φ (jBarGen N) = ψ (jBarGen N)) (h2 : φ (jNBarGen N) = ψ (jNBarGen N)) : φ = ψ := by

  let T : IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (AlgHom.equalizer φ ψ).toIntermediateField (fun x hx => by
      rw [AlgHom.mem_equalizer] at hx ⊢
      rw [map_inv₀, map_inv₀, hx])
  have hle : IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jBarGen N, jNBarGen N} : Set (modularFunctionFieldBar N)) ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  rw [adjoin_gens_eq_top] at hle
  refine AlgHom.ext fun x => ?_
  have hx : x ∈ T := hle IntermediateField.mem_top
  exact hx

theorem fricke_fricke (hσ : IsFrickeBar N σ) (x : modularFunctionFieldBar N) : σ (σ x) = x := by
  have key : (σ.trans σ).toAlgHom = AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
    refine algHom_ext_gens ?_ ?_
    · show σ (σ (jBarGen N)) = jBarGen N
      rw [fricke_jBarGen hσ, fricke_jNBarGen hσ]
    · show σ (σ (jNBarGen N)) = jNBarGen N
      rw [fricke_jNBarGen hσ, fricke_jBarGen hσ]
  exact AlgHom.congr_fun key x

theorem fricke_smul_fricke_smul (hσ : IsFrickeBar N σ) (z : JZero N) :
    SemilinearAut.ofAlgAut σ • (SemilinearAut.ofAlgAut σ • z) = z := by
  have hσσ : σ * σ = 1 :=
    AlgEquiv.ext fun x => (AlgEquiv.mul_apply σ σ x).trans ((fricke_fricke hσ x).trans (AlgEquiv.one_apply x).symm)
  rw [← mul_smul, ← map_mul, hσσ, map_one, one_smul]

theorem arithmeticRingAut_jBarGen (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticRingAut (modularFunctionFieldFull N) τ (jBarGen N) = jBarGen N :=
  Subtype.ext (coeffMap_coeffEmb τ jq)

theorem arithmeticRingAut_jNBarGen (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticRingAut (modularFunctionFieldFull N) τ (jNBarGen N) = jNBarGen N :=
  Subtype.ext (coeffMap_coeffEmb τ (qExpand ℚ N jq))

theorem arithmeticRingAut_fricke (hσ : IsFrickeBar N σ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : modularFunctionFieldBar N) :
    arithmeticRingAut (modularFunctionFieldFull N) τ (σ x) = σ (arithmeticRingAut (modularFunctionFieldFull N) τ x) := by

  let ψ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
    { (((arithmeticRingAut (modularFunctionFieldFull N) τ).symm : modularFunctionFieldBar N ≃+* modularFunctionFieldBar N) :
          modularFunctionFieldBar N →+* modularFunctionFieldBar N).comp
        ((σ : modularFunctionFieldBar N →+* modularFunctionFieldBar N).comp
          ((arithmeticRingAut (modularFunctionFieldFull N) τ : modularFunctionFieldBar N ≃+* modularFunctionFieldBar N) :
            modularFunctionFieldBar N →+* modularFunctionFieldBar N)) with
      commutes' := fun c => by
        show (arithmeticRingAut (modularFunctionFieldFull N) τ).symm (σ (arithmeticRingAut (modularFunctionFieldFull N) τ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)))
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
        rw [arithmeticRingAut_algebraMap, AlgEquiv.commutes, RingEquiv.symm_apply_eq,
          arithmeticRingAut_algebraMap] }
  have key : ψ = σ.toAlgHom := by
    refine algHom_ext_gens ?_ ?_
    · show (arithmeticRingAut (modularFunctionFieldFull N) τ).symm (σ (arithmeticRingAut (modularFunctionFieldFull N) τ (jBarGen N))) = σ (jBarGen N)
      rw [arithmeticRingAut_jBarGen, fricke_jBarGen hσ, RingEquiv.symm_apply_eq, arithmeticRingAut_jNBarGen]
    · show (arithmeticRingAut (modularFunctionFieldFull N) τ).symm (σ (arithmeticRingAut (modularFunctionFieldFull N) τ (jNBarGen N))) = σ (jNBarGen N)
      rw [arithmeticRingAut_jNBarGen, fricke_jNBarGen hσ, RingEquiv.symm_apply_eq, arithmeticRingAut_jBarGen]
  have hx : (arithmeticRingAut (modularFunctionFieldFull N) τ).symm (σ (arithmeticRingAut (modularFunctionFieldFull N) τ x)) = σ x := AlgHom.congr_fun key x
  rw [RingEquiv.symm_apply_eq] at hx
  exact hx.symm

theorem arithmeticGalois_mul_ofAlgAut (hσ : IsFrickeBar N σ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull N) τ * SemilinearAut.ofAlgAut σ
      = SemilinearAut.ofAlgAut σ * arithmeticGalois (modularFunctionFieldFull N) τ := by
  refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => ?_) ?_)
  · exact arithmeticRingAut_fricke hσ τ x
  · show τ.toRingEquiv * 1 = 1 * τ.toRingEquiv
    rw [mul_one, one_mul]

theorem galois_smul_fricke_smul (hσ : IsFrickeBar N σ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (z : JZero N) :
    τ • (SemilinearAut.ofAlgAut σ • z) = SemilinearAut.ofAlgAut σ • (τ • z) := by
  rw [galois_smul_pic0_def, galois_smul_pic0_def, ← mul_smul, ← mul_smul, arithmeticGalois_mul_ofAlgAut hσ]

end Fricke

section FrobLevel

variable {N : ℕ} [NeZero N] {n : ℕ} [NeZero n]
variable {σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N}

theorem pair_galois_fricke [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    (hσ : IsFrickeBar N σ)
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (hgal : ∀ (g : SemilinearAut (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (x y : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n),
        e.pair (g • x) (g • y) = SemilinearAut.baseAut g (e.pair x y))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x y τx wy wτy : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (hτx : (τx : JZero N) = τ • (x : JZero N))
    (hwy : (wy : JZero N) = SemilinearAut.ofAlgAut σ • (y : JZero N))
    (hwτy : (wτy : JZero N) = SemilinearAut.ofAlgAut σ • (τ • (y : JZero N))) :
    e.pair τx wτy = τ (e.pair x wy) := by
  have h1 : τx = arithmeticGalois (modularFunctionFieldFull N) τ • x :=
    Subtype.ext (by rw [SemilinearAut.coe_torsion_smul, hτx, galois_smul_pic0_def])
  have h2 : wτy = arithmeticGalois (modularFunctionFieldFull N) τ • wy :=
    Subtype.ext (by
      rw [SemilinearAut.coe_torsion_smul, hwτy, hwy, ← galois_smul_fricke_smul hσ, galois_smul_pic0_def])
  rw [h1, h2, hgal]
  rfl

end FrobLevel

end ModularCurve.PEdge

theorem solution (N : ℕ) [NeZero N]
    (σ : ModularCurve.modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] ModularCurve.modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : ModularCurve.modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ a ModularCurve.jq) →
          ((σ x : ModularCurve.modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ b ModularCurve.jq))
    (z : ModularCurve.JZero N) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • (AlgebraicCurve.SemilinearAut.ofAlgAut σ • z) = z :=
  ModularCurve.PEdge.fricke_smul_fricke_smul hσ z

end

end S_ModularCurve_ofAlgAut_smul_ofAlgAut_smul_of_fricke
end P2MW
export P2MW.S_ModularCurve_ofAlgAut_smul_ofAlgAut_smul_of_fricke (solution)
