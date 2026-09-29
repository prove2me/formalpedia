-- Prove2me | solution 1 for ModularCurve.mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/336a435e-0d65-5476-af45-a87b04753ee5

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_ModularCurve_JZero_isOpen_stabilizer
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option Elab.async false

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "heckeModuleBar JZero HeckeAlg heckeTorsion mTorsionGaloisRep coe_mTorsionGaloisRep_apply JZero.isOpen_stabilizer"
p2m_open "ModularCurve"

private theorem gftfl_of_finite_openStab
    {J : Type*} [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    (hopen : ∀ y : J, IsOpen (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) y :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    {X : Type*} [Finite X] (c : X → J)
    {M : Type} [MulOneClass M] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (hρ : ∀ σ, (∀ x : X, σ • c x = c x) → ρ σ = 1) :
    GaloisFactorsThroughFiniteLevel ρ := by
  set G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ
  have hSopen : IsOpen (⋂ x : X, (MulAction.stabilizer G (c x) : Set G)) :=
    isOpen_iInter_of_finite fun x => hopen (c x)
  have hSone : (1 : G) ∈ ⋂ x : X, (MulAction.stabilizer G (c x) : Set G) :=
    Set.mem_iInter.2 fun x => Subgroup.one_mem _
  obtain ⟨E, hEfin, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).1 (hSopen.mem_nhds hSone)
  refine ⟨E, hEfin, fun σ hσ => hρ σ fun x => ?_⟩
  have hσfix : σ ∈ E.fixingSubgroup := (E.mem_fixingSubgroup_iff σ).2 hσ
  exact MulAction.mem_stabilizer_iff.1 (Set.mem_iInter.1 (hEsub hσfix) x)

private theorem mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel (M : ℕ) [NeZero M]
    (𝔪 : Ideal HeckeAlg)
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))
    (hfin : letI := heckeModuleBar M; Finite (heckeTorsion (JZero M) 𝔪)) :
    letI := heckeModuleBar M; haveI := hsmc
    GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero M) 𝔪) := by
  letI := heckeModuleBar M; haveI := hsmc; haveI := hfin
  exact gftfl_of_finite_openStab (JZero.isOpen_stabilizer M)
    (fun x : heckeTorsion (JZero M) 𝔪 => (x : JZero M)) _
    (fun σ hσ => LinearMap.ext fun x => Subtype.ext (by simpa using hσ x))

#check @mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel

end ModularCurve

set_option autoImplicit false
open AlgebraicCurve
p2m_open "ModularCurve P2MW.S_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel.ModularCurve"

theorem solution (M : ℕ) [NeZero M]
    (𝔪 : Ideal HeckeAlg)
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))
    (hfin : letI := heckeModuleBar M; Finite (heckeTorsion (JZero M) 𝔪)) :
    letI := heckeModuleBar M; haveI := hsmc
    GaloisFactorsThroughFiniteLevel
      (mTorsionGaloisRep (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (JZero M) 𝔪) := by
  exact ModularCurve.mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel M 𝔪 hsmc hfin

end S_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel
end P2MW
export P2MW.S_ModularCurve_mTorsionGaloisRep_jZero_galoisFactorsThroughFiniteLevel (solution)
