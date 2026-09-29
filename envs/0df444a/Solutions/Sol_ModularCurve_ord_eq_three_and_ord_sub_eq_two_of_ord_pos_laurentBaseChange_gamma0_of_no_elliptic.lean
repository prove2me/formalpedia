-- Prove2me | solution 1 for ModularCurve.ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d66e407b-8b81-5454-939a-598413f6d696

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic_algebraicClosure
import Theorems.Thm_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic.ModularCurve"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC intFormRatiosC_subset coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff jqModC map_jqModC ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic_algebraicClosure exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange jqModC_mem_intFormRatiosC"
namespace NoEllK
p2m_open "ModularCurve"

section CoeffLift

variable {L : Type*} [Field L] {Ω : Type*} [Field Ω] [Algebra ℚ L] [Algebra ℚ Ω] (τ : L →ₐ[ℚ] Ω)
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_coeffEmb' (x : LaurentSeries ℚ) : coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x := by
  change coeffMap _ (coeffMap _ x) = coeffMap _ x
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) x

theorem coeffMap_algebraMap' (c : L) :
    coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap Ω (LaurentSeries Ω) (τ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

theorem coeffMap_mem_laurentBaseChange' {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap τ.toRingHom x ∈ laurentBaseChange Ω F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange Ω F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange Ω hz
  | one => simp
  | add _ _ _ _ hx hy => simpa using add_mem hx hy
  | neg _ _ hx => simpa using neg_mem hx
  | inv _ _ hx => simpa using inv_mem hx
  | mul _ _ _ _ hx hy => simpa using mul_mem hx hy

def liftRingHom : ↥(laurentBaseChange L F₀) →+* ↥(laurentBaseChange Ω F₀) :=
  ((coeffMap τ.toRingHom).comp (laurentBaseChange L F₀).toSubring.subtype).codRestrict
    (laurentBaseChange Ω F₀).toSubring (fun x => coeffMap_mem_laurentBaseChange' τ F₀ x.2)

theorem coe_liftRingHom (x : ↥(laurentBaseChange L F₀)) :
    ((liftRingHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) = coeffMap τ.toRingHom x :=
  rfl

end CoeffLift

end ModularCurve.NoEllK

open ModularCurve.NoEllK in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (N : ℕ) [NeZero N]
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :

    ((9 ∣ N ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ ℓ % 3 = 2) →
      ∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))),
        0 < P.ord y → P.ord y = 3) ∧

    ((4 ∣ N ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ ℓ % 4 = 3) →
      ∀ P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))),
        0 < P.ord (y - 1728) → P.ord (y - 1728) = 2) := by
  classical
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    constructor
    intro x
    obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x
    refine ⟨p, hp0, ?_⟩
    rw [Polynomial.aeval_def] at hp ⊢
    convert hp using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  let τ : AlgebraicClosure ℚ →ₐ[ℚ] K := IsAlgClosed.lift
  let F₀ : IntermediateField ℚ (LaurentSeries ℚ) := ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)
  let Ψ := liftRingHom τ F₀
  have hΨ : ∀ f, ((Ψ f : ↥(ModularCurve.laurentBaseChange K F₀)) : LaurentSeries K) =
      ModularCurve.coeffMap τ.toRingHom (f : LaurentSeries (AlgebraicClosure ℚ)) := fun f => rfl

  have hjmem : ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.jqModC ℚ) ∈
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀ :=
    ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 N)))
  let y₀ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀) := ⟨_, hjmem⟩
  have hy₀ : (y₀ : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) := by
    show ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.jqModC ℚ) = _
    exact ModularCurve.map_jqModC _
  have hΨy : Ψ y₀ = y := by
    apply Subtype.ext
    rw [hΨ, hy₀, hy]
    exact ModularCurve.map_jqModC _
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨fun h3 P hpos => ?_, fun h2 P hpos => ?_⟩
  · rw [← hΨy] at hpos ⊢
    obtain ⟨P₀, hP₀⟩ := ModularCurve.exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange K
      (CongruenceSubgroup.Gamma0 N) hT τ Ψ hΨ P ⟨y₀, hpos.ne'⟩
    rw [hP₀] at hpos ⊢
    exact (ModularCurve.ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic_algebraicClosure N
      y₀ hy₀).1 h3 P₀ hpos
  · have hsub : y - 1728 = Ψ (y₀ - 1728) := by rw [map_sub, map_ofNat, hΨy]
    rw [hsub] at hpos ⊢
    obtain ⟨P₀, hP₀⟩ := ModularCurve.exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange K
      (CongruenceSubgroup.Gamma0 N) hT τ Ψ hΨ P ⟨y₀ - 1728, hpos.ne'⟩
    rw [hP₀] at hpos ⊢
    exact (ModularCurve.ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic_algebraicClosure N
      y₀ hy₀).2 h2 P₀ hpos

end
end S_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic
end P2MW
export P2MW.S_ModularCurve_ord_eq_three_and_ord_sub_eq_two_of_ord_pos_laurentBaseChange_gamma0_of_no_elliptic (solution)
