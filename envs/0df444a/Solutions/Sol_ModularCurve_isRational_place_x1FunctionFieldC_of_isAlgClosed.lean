-- Prove2me | solution 1 for ModularCurve.isRational_place_x1FunctionFieldC_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c4d76588-a94a-5bdb-9cb3-d9c22aff841f

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve AlgebraicCurve Polynomial

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω]
    (v : AlgebraicCurve.Place Ω ↥(ModularCurve.x1FunctionFieldC Ω M)) : v.IsRational := by
  classical
  obtain ⟨t, ht, htr, hfd, -⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM Ω

  let φ : (Polynomial Ω) →ₐ[Ω] ↥(ModularCurve.x1FunctionFieldC Ω M) := Polynomial.aeval t
  have hφinj : Function.Injective φ := (transcendental_iff_injective.mp htr)
  have hφ : nonZeroDivisors (Polynomial Ω) ≤ (nonZeroDivisors ↥(ModularCurve.x1FunctionFieldC Ω M)).comap φ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφinj
  let ψ : RatFunc Ω →ₐ[Ω] ↥(ModularCurve.x1FunctionFieldC Ω M) := RatFunc.liftAlgHom φ hφ
  letI : Algebra (RatFunc Ω) ↥(ModularCurve.x1FunctionFieldC Ω M) := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower Ω (RatFunc Ω) ↥(ModularCurve.x1FunctionFieldC Ω M) :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have hψX : ψ (algebraMap (Polynomial Ω) (RatFunc Ω) X) = t := by
    rw [show algebraMap (Polynomial Ω) (RatFunc Ω) X = algebraMap (Polynomial Ω) (RatFunc Ω) X / algebraMap (Polynomial Ω) (RatFunc Ω) 1 by
      rw [map_one, div_one], RatFunc.liftAlgHom_apply_div, map_one, div_one]
    exact Polynomial.aeval_X t

  set E := IntermediateField.adjoin Ω ({t} : Set ↥(ModularCurve.x1FunctionFieldC Ω M)) with hE
  have hEle : E ≤ ψ.fieldRange := by
    rw [hE, IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨_, hψX⟩
  haveI : FiniteDimensional (RatFunc Ω) ↥(ModularCurve.x1FunctionFieldC Ω M) := by
    haveI := hfd
    obtain ⟨s, hs⟩ := Module.finite_def.mp hfd
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ Submodule.span (↥E) (s : Set ↥(ModularCurve.x1FunctionFieldC Ω M)) := by rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun w _ => w ∈ Submodule.span (RatFunc Ω) (s : Set ↥(ModularCurve.x1FunctionFieldC Ω M))) ?_ ?_ ?_ ?_ hv
    · intro w hw; exact Submodule.subset_span hw
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro e w _ hw
      obtain ⟨r, hr⟩ := hEle e.2
      have : (e • w : ↥(ModularCurve.x1FunctionFieldC Ω M)) = r • w := by
        show (e : ↥(ModularCurve.x1FunctionFieldC Ω M)) * w = ψ r * w
        rw [← hr]; rfl
      rw [this]
      exact Submodule.smul_mem _ r hw
  exact AlgebraicCurve.Place.isRational_of_isAlgClosed v

end S_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed (solution)
