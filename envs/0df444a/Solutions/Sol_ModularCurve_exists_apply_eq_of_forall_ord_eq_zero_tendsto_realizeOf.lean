-- Prove2me | solution 1 for ModularCurve.exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/781b93e0-8ab9-58b2-894d-c8ea49f426de

import Mathlib
import Theorems.Thm_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (y : ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (Pl : SL(2, ℤ) → AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀))
    (hΓPl : ∀ γ ∈ Γ, ∀ σ : SL(2, ℤ), Pl (γ * σ) = Pl σ)
    (hlim : ∀ (σ : SL(2, ℤ)) (x : ↥(ModularCurve.laurentBaseChange ℂ F₀)), x ≠ 0 → (Pl σ).ord x = 0 →
      ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ))
          UpperHalfPlane.atImInfty (nhds L))
    (P : AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hP : y ∉ P.toValuationSubring) :
    ∃ σ : SL(2, ℤ), Pl σ = P := by
  classical
  by_contra hcon
  push_neg at hcon

  let Pl' : Quotient (QuotientGroup.rightRel Γ) → AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀) :=
    Quotient.lift Pl (by
      intro a b hab
      have hab' : b * a⁻¹ ∈ Γ := QuotientGroup.rightRel_apply.mp hab
      have h := hΓPl (b * a⁻¹) hab' a
      rw [inv_mul_cancel_right] at h
      exact h.symm)
  haveI : Finite (Quotient (QuotientGroup.rightRel Γ)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ).symm
  have hfin : (Set.range Pl).Finite := by
    refine (Set.finite_range Pl').subset ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨Quotient.mk _ σ, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀)),
      ∀ σ, Pl σ ∈ S₀ := ⟨hfin.toFinset, fun σ => hfin.mem_toFinset.mpr ⟨σ, rfl⟩⟩

  obtain ⟨g, hg0, hg⟩ := AlgebraicCurve.Place.exists_forall_ord_eq_finset (insert P S₀)
    (fun v => if v = P then (1 : ℤ) else 0)
  have hPg : P.ord g = 1 := by
    have h := hg P (Finset.mem_insert_self P S₀)
    rwa [if_pos rfl] at h
  have hσg : ∀ σ : SL(2, ℤ), (Pl σ).ord g = 0 := fun σ => by
    have h := hg (Pl σ) (Finset.mem_insert_of_mem (hS₀ σ))
    rwa [if_neg (hcon σ)] at h

  have hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (g : LaurentSeries ℂ) (σ • τ)) UpperHalfPlane.atImInfty (nhds L) :=
    fun σ => hlim σ g hg0 (hσg σ)

  have h0 : P.ord g = 0 :=
    ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto Γ hT hΓ F₀ hF g
      (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (g : LaurentSeries ℂ) τ) (fun τ => Filter.EventuallyEq.rfl) hcusp P y hy hP
  rw [h0] at hPg
  exact zero_ne_one hPg

end S_ModularCurve_exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf
end P2MW
export P2MW.S_ModularCurve_exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf (solution)
