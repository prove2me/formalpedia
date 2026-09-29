-- Prove2me | solution 1 for ModularCurve.exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a2f06fc4-cca6-505f-8aee-b5bd374afa30

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_evalAt_eq_apply_evalAt_of_coe_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (An : AlgebraicCurve.Annulus A ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hz : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • An.param = An.param)
    (hdom : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W ∈ An.dom,
      arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • W ∈ An.dom)
    (c : ↥A) (hc : c ∈ maximalIdeal ↥A) (hc0 : (c : AlgebraicClosure ℚ) ≠ 0)
    (hcm : ∃ m ∈ maximalIdeal ↥A, ((An.modulus : ↥A) : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ) * m)
    (hcσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (c : AlgebraicClosure ℚ) = c) :
    ∃ W ∈ An.dom,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • W = W) ∧
      W.evalAt An.param = (c : AlgebraicClosure ℚ) := by
  obtain ⟨W, ⟨hWdom, hWc⟩, huniq⟩ := An.existsUnique_evalAt_eq c hc hc0 hcm
  refine ⟨W, hWdom, fun σ hσ => ?_, hWc⟩
  obtain ⟨hrat, hzO, -⟩ := An.mem_dom W hWdom

  have hval : (arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • W).evalAt An.param = (c : AlgebraicClosure ℚ) := by
    have h := ModularCurve.evalAt_eq_apply_evalAt_of_coe_eq_coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) F₀ W
      (arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • W) ?_ hrat An.param An.param ?_ hzO
    · rw [h, hWc]
      exact hcσ σ hσ
    · intro x x' hx'
      have hxx : x' = arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • x :=
        Subtype.ext (hx'.trans (coe_arithmeticGalois_smul _ σ x).symm)
      rw [hxx]
      exact SemilinearAut.ord_smul _ W x
    · rw [← coe_arithmeticGalois_smul _ σ An.param, hz σ hσ]
  exact huniq _ ⟨hdom σ hσ W hWdom, hval⟩

end S_ModularCurve_exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq
end P2MW
export P2MW.S_ModularCurve_exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq (solution)
