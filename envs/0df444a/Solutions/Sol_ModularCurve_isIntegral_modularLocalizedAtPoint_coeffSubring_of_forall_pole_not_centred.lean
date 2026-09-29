-- Prove2me | solution 1 for ModularCurve.isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/27efc929-8775-52b2-9bee-c70170e58cd9

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
import Theorems.Thm_ModularCurve_exists_numberField_presentation
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherian_and_isLocalization
import Theorems.Thm_ModularCurve_exists_mul_eq_of_height_one_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_Ideal_finite_setOf_height_eq_one_and_mem
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_IsDiscreteValuationRing_exists_pow_mul_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred.ModularCurve"
open ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularLocalized coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC qExpand qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full frickeInvolutionBar modularFunctionFieldBar jIntegralClosure_isNoetherian_and_isLocalization exists_mul_eq_of_height_one_of_forall_pole_not_centred NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero exists_kroneckerCongruence_of_prime ModularPolynomialData.eval_jqNModC_mul_eq_zero"
p2m_open "ModularCurve"
section Assembly
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k]

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

theorem modularLocalizedAtPoint_coeffSubring_le (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a b : k) :
    modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a b
      ≤ modularLocalizedAtPoint (1 * q) A.toSubring red a b := by
  rintro x ⟨r, s, hs, hxs⟩
  let ι : ↥(coeffSubring A K) →+* ↥A.toSubring := Subring.inclusion inf_le_left
  refine ⟨MvPolynomial.map ι r, MvPolynomial.map ι s, ?_, ?_⟩
  ·
    have : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        pointEval A.toSubring red a b (MvPolynomial.map ι p) = pointEval (coeffSubring A K) (redRestrict red K) a b p := fun p => by
      rw [pointEval, pointEval, MvPolynomial.eval₂Hom_map_hom]; rfl
    rw [this]; exact hs
  · have : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        modularEval (1 * q) A.toSubring (MvPolynomial.map ι p) = modularEval (1 * q) (coeffSubring A K) p := fun p => by
      rw [modularEval, modularEval, MvPolynomial.eval₂Hom_map_hom]; rfl
    rw [this, this]; exact hxs

theorem isIntegral_of_subring_le {R₀ R : Subring LQ} (h : R₀ ≤ R) {x : LQ} (hx : IsIntegral ↥R₀ x) : IsIntegral ↥R x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (Subring.inclusion h), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpx

end Assembly

section PerPrime

theorem exists_pow_mul_presentation_of_height_eq_one
    {C : Type*} [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    (𝔭 : Ideal C) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (t : C) (ht : t ∈ 𝔭) (ht0 : t ≠ 0) (x : K) :
    ∃ N : ℕ, ∃ r s : C, s ∉ 𝔭 ∧ algebraMap C K t ^ N * x * algebraMap C K s = algebraMap C K r := by
  classical
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one 𝔭 h𝔭
  have hle : 𝔭.primeCompl ≤ nonZeroDivisors C := 𝔭.primeCompl_le_nonZeroDivisors
  have hunits : ∀ y : 𝔭.primeCompl, IsUnit (algebraMap C K y) := fun y =>
    IsUnit.mk0 _ (fun h => nonZeroDivisors.ne_zero (hle y.2) ((FaithfulSMul.algebraMap_injective C K) (by rw [h, map_zero])))
  letI : Algebra (Localization.AtPrime 𝔭) K :=
    (IsLocalization.lift (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) (g := algebraMap C K) hunits).toAlgebra
  haveI : IsScalarTower C (Localization.AtPrime 𝔭) K := IsScalarTower.of_algebraMap_eq (fun c =>
    (IsLocalization.lift_eq (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) hunits c).symm)
  haveI : IsFractionRing (Localization.AtPrime 𝔭) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl (Localization.AtPrime 𝔭) K
  have ht' : algebraMap C (Localization.AtPrime 𝔭) t ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 t).mpr ht
  have ht0' : algebraMap C (Localization.AtPrime 𝔭) t ≠ 0 := fun h =>
    ht0 (IsLocalization.injective (Localization.AtPrime 𝔭) hle (by rw [h, map_zero]))
  obtain ⟨N, r', hr'⟩ := IsDiscreteValuationRing.exists_pow_mul_mem_range K _ ht0' ht' x
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl r'
  refine ⟨N, r, s, s.2, ?_⟩
  have hK : algebraMap (Localization.AtPrime 𝔭) K (algebraMap C (Localization.AtPrime 𝔭) t) = algebraMap C K t :=
    (IsScalarTower.algebraMap_apply C (Localization.AtPrime 𝔭) K t).symm
  rw [hK] at hr'
  rw [← hr', ← hrs]

  have hspec := IsLocalization.mk'_spec (Localization.AtPrime 𝔭) r s
  have := congrArg (algebraMap (Localization.AtPrime 𝔭) K) hspec
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  exact this

end PerPrime

section Assembly2
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k]

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

theorem modularEval_coeffSubring_mem_fieldOver (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval N (coeffSubring A K) p ∈ fieldOver N K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    refine Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), ?_⟩, rfl⟩)
    exact (c.2).2
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    rw [modularEval, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · exact Subfield.subset_closure (Or.inr (Or.inl rfl))
    · exact Subfield.subset_closure (Or.inr (Or.inr rfl))

theorem jRing_le_fieldOver (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] :
    jRing A K ≤ (fieldOver N K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), (c.2).2⟩, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx; subst hx
    exact Subfield.subset_closure (Or.inr (Or.inl rfl))

theorem jRing_le_jIntegralClosure (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] :
    jRing A K ≤ jIntegralClosure N A K := fun x hx =>
  ⟨jRing_le_fieldOver A K N hx, isIntegral_algebraMap (R := ↥(jRing A K)) (A := LaurentSeries (AlgebraicClosure ℚ)) (x := ⟨x, hx⟩)⟩

theorem isIntegral_jRing_jqNModC (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) :
    IsIntegral ↥(jRing A K) (jqNModC (AlgebraicClosure ℚ) (1 * q)) := by
  have hj : jqModC (AlgebraicClosure ℚ) ∈ jRing A K := Subring.subset_closure (Or.inr rfl)

  let φ : Polynomial ℤ →+* ↥(jRing A K) := Polynomial.eval₂RingHom (Int.castRingHom _) ⟨_, hj⟩
  refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  have h0 := ModularPolynomialData.eval_jqNModC_mul_eq_zero data (AlgebraicClosure ℚ) 1

  have hcomp : (algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ))).comp φ
      = (Polynomial.aeval (R := ℤ) (jqNModC (AlgebraicClosure ℚ) 1)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro n; simp [φ]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      show ((φ Polynomial.X : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) 1
      rw [show φ Polynomial.X = ⟨_, hj⟩ from Polynomial.eval₂_X _ _]
      exact (qExpand_one_apply _).symm
  rw [hcomp]
  exact h0

theorem modularEval_coeffSubring_mem_jIntegralClosure (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (data : ModularPolynomialData q) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ jIntegralClosure (1 * q) A K := by
  refine ⟨modularEval_coeffSubring_mem_fieldOver A K (1 * q) p, ?_⟩
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, Subring.subset_closure (Or.inl ⟨c, rfl⟩)⟩)
  | add p r hp hr => rw [map_add]; exact hp.add hr
  | mul_X p i hp =>
    rw [map_mul]
    refine hp.mul ?_
    rw [modularEval, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, Subring.subset_closure (Or.inr rfl)⟩)
    · exact isIntegral_jRing_jqNModC A K data

theorem _root_.P2MW.S_ModularCurve_isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred.solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f < 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    IsIntegral ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
      (f : LaurentSeries (AlgebraicClosure ℚ)) := by
  classical
  obtain ⟨data, -⟩ := ModularCurve.exists_kroneckerCongruence_of_prime q
  obtain ⟨hnoeth, hic, hfrac, hloc⟩ := ModularCurve.jIntegralClosure_isNoetherian_and_isLocalization red a data K
  set C := jIntegralClosure (1 * q) A K with hCdef
  set F₀ := fieldOver (1 * q) K with hF₀def
  have hfF₀ : (f : LQ) ∈ F₀ := hf

  have hCF : C ≤ F₀.toSubring := fun x hx => hx.1
  letI : Algebra ↥C ↥F₀ := (Subring.inclusion hCF).toAlgebra
  haveI : IsNoetherianRing ↥C := hnoeth
  haveI : IsIntegrallyClosed ↥C := hic
  haveI : IsFractionRing ↥C ↥F₀ := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      have hy0 : (y : LQ) ≠ 0 := fun h => nonZeroDivisors.ne_zero hy (Subtype.ext h)
      exact isUnit_iff_ne_zero.mpr (fun h => hy0 (congrArg Subtype.val h))
    · intro z
      obtain ⟨c, s, hc, hs, hs0, hzs⟩ := hfrac z.1 z.2
      have hsC : s ∈ C := jRing_le_jIntegralClosure A K (1 * q) hs
      refine ⟨⟨⟨c, hc⟩, ⟨⟨s, hsC⟩, mem_nonZeroDivisors_of_ne_zero (fun h => hs0 (congrArg Subtype.val h))⟩⟩, ?_⟩
      exact Subtype.ext hzs
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : LQ) = y := congrArg (fun z : ↥F₀ => (z : LQ)) hxy
      rw [Subtype.ext this]

  set A₀ := coeffSubring A K with hA₀
  set red₀ := redRestrict red K with hred₀
  let mE : MvPolynomial (Fin 2) ↥A₀ →+* LQ := modularEval (1 * q) A₀
  let pE : MvPolynomial (Fin 2) ↥A₀ →+* k := pointEval A₀ red₀ a (a ^ q)
  have hmEC : ∀ p, mE p ∈ C := fun p => modularEval_coeffSubring_mem_jIntegralClosure A K data p
  let xF : ↥F₀ := ⟨(f : LQ), hfF₀⟩

  have hper : ∀ (𝔭 : Ideal ↥C), 𝔭.IsPrime → 𝔭.height = 1 →
      ∃ (s' : MvPolynomial (Fin 2) ↥A₀) (N : ℕ), pE s' ≠ 0 ∧
        ∃ r t : ↥C, t ∉ 𝔭 ∧ (mE s') ^ N * (f : LQ) * (t : LQ) = r := by
    intro 𝔭 h𝔭p h𝔭h
    haveI := h𝔭p
    by_cases hnd : ∃ s' : MvPolynomial (Fin 2) ↥A₀, pE s' ≠ 0 ∧ mE s' ≠ 0 ∧ (⟨mE s', hmEC s'⟩ : ↥C) ∈ 𝔭
    · obtain ⟨s', hps', hms', hmem⟩ := hnd
      have ht0 : (⟨mE s', hmEC s'⟩ : ↥C) ≠ 0 := fun h => hms' (congrArg Subtype.val h)
      obtain ⟨N, r, t, ht, hNr⟩ := exists_pow_mul_presentation_of_height_eq_one ↥F₀ 𝔭 h𝔭h ⟨mE s', hmEC s'⟩ hmem ht0 xF
      refine ⟨s', N, hps', r, t, ht, ?_⟩
      exact congrArg (fun z : ↥F₀ => (z : LQ)) hNr
    ·
      have h𝔭S : ∀ s : MvPolynomial (Fin 2) ↥A₀, pE s ≠ 0 → ∀ hs : mE s ∈ C, (⟨_, hs⟩ : ↥C) ∉ 𝔭 := by
        intro s hps hs hmem
        have hms : mE s ≠ 0 := fun h0 => hps (ModularCurve.NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero red a K s h0)
        exact hnd ⟨s, hps, hms, hmem⟩
      obtain ⟨r, t, ht, hft⟩ := ModularCurve.exists_mul_eq_of_height_one_of_forall_pole_not_centred red a K 𝔭 h𝔭h h𝔭S f hfF₀ h₁ h₂ hpole
      refine ⟨1, 0, by rw [map_one]; exact one_ne_zero, r, t, ht, ?_⟩
      rw [pow_zero, one_mul]; exact hft
  choose S' Nf hS' using hper

  obtain ⟨c₀, s₁, hc₀, hs₁, hs₁0, hfs₁⟩ := hfrac (f : LQ) hfF₀
  have hs₁C : s₁ ∈ C := jRing_le_jIntegralClosure A K (1 * q) hs₁
  have hfin := Ideal.finite_setOf_height_eq_one_and_mem (R := ↥C) (b := ⟨s₁, hs₁C⟩) (fun h => hs₁0 (congrArg Subtype.val h))
  let T : Finset (Ideal ↥C) := hfin.toFinset

  let g : Ideal ↥C → MvPolynomial (Fin 2) ↥A₀ := fun 𝔭 =>
    if h : 𝔭.IsPrime ∧ 𝔭.height = 1 then (S' 𝔭 h.1 h.2) ^ (Nf 𝔭 h.1 h.2) else 1
  have hg_ne : ∀ 𝔭, pE (g 𝔭) ≠ 0 := by
    intro 𝔭
    simp only [g]
    split_ifs with h
    · rw [map_pow]; exact pow_ne_zero _ (hS' 𝔭 h.1 h.2).1
    · rw [map_one]; exact one_ne_zero
  have hclear : ∃ s : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0 ∧
      ∀ (𝔭 : Ideal ↥C) [𝔭.IsPrime], 𝔭.height = 1 →
        ∃ r t : ↥C, t ∉ 𝔭 ∧ (⟨(f : LQ) * modularEval (1 * q) (coeffSubring A K) s,
          mul_mem hfF₀ (modularEval_coeffSubring_mem_fieldOver A K (1 * q) s)⟩ : ↥F₀) * algebraMap ↥C ↥F₀ t = algebraMap ↥C ↥F₀ r := by
    refine ⟨∏ 𝔭 ∈ T, g 𝔭, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ => hg_ne 𝔭)
    · intro 𝔭 h𝔭p h𝔭h
      by_cases hpol : (⟨s₁, hs₁C⟩ : ↥C) ∈ 𝔭
      ·
        have h𝔭T : 𝔭 ∈ T := hfin.mem_toFinset.mpr ⟨h𝔭p, h𝔭h, hpol⟩
        obtain ⟨r, t, ht, hrt⟩ := (hS' 𝔭 h𝔭p h𝔭h).2
        have hgp : g 𝔭 = (S' 𝔭 h𝔭p h𝔭h) ^ (Nf 𝔭 h𝔭p h𝔭h) := by simp only [g, dif_pos (And.intro h𝔭p h𝔭h)]

        have hco : mE (∏ 𝔮 ∈ T.erase 𝔭, g 𝔮) ∈ C := hmEC _
        refine ⟨r * ⟨_, hco⟩, t, ht, Subtype.ext ?_⟩
        show (f : LQ) * mE (∏ 𝔮 ∈ T, g 𝔮) * (t : LQ) = (r : LQ) * mE (∏ 𝔮 ∈ T.erase 𝔭, g 𝔮)
        rw [← Finset.mul_prod_erase T g h𝔭T, map_mul, hgp, map_pow]
        calc (f : LQ) * ((mE (S' 𝔭 h𝔭p h𝔭h)) ^ (Nf 𝔭 h𝔭p h𝔭h) * mE (∏ 𝔮 ∈ T.erase 𝔭, g 𝔮)) * (t : LQ)
            = ((mE (S' 𝔭 h𝔭p h𝔭h)) ^ (Nf 𝔭 h𝔭p h𝔭h) * (f : LQ) * (t : LQ)) * mE (∏ 𝔮 ∈ T.erase 𝔭, g 𝔮) := by ring
          _ = (r : LQ) * mE (∏ 𝔮 ∈ T.erase 𝔭, g 𝔮) := by rw [hrt]
      ·
        refine ⟨⟨c₀, hc₀⟩ * ⟨_, hmEC (∏ 𝔮 ∈ T, g 𝔮)⟩, ⟨s₁, hs₁C⟩, hpol, Subtype.ext ?_⟩
        show (f : LQ) * mE (∏ 𝔮 ∈ T, g 𝔮) * s₁ = c₀ * mE (∏ 𝔮 ∈ T, g 𝔮)
        calc (f : LQ) * mE (∏ 𝔮 ∈ T, g 𝔮) * s₁ = ((f : LQ) * s₁) * mE (∏ 𝔮 ∈ T, g 𝔮) := by ring
          _ = c₀ * mE (∏ 𝔮 ∈ T, g 𝔮) := by rw [hfs₁]
  obtain ⟨s, hs, hall⟩ := hclear

  obtain ⟨c, hc⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one ↥F₀ _ (fun 𝔭 _ h𝔭 => hall 𝔭 h𝔭)

  refine ((hloc (f : LQ)).mpr ⟨(c : LQ), s, c.2, hs, ?_⟩).2
  have := congrArg (fun z : ↥F₀ => (z : LQ)) hc
  exact this.symm

end Assembly2
end ModularCurve

end S_ModularCurve_isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred
end P2MW
export P2MW.S_ModularCurve_isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred (solution)
