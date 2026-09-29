-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_of_involutive_subst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/493aa4b0-0edb-5484-8110-eddc72754517

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Theorems.Thm_ModularCurve_minpoly_lambdaNModC_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst.ModularCurve.LambdaNodeLocalized"
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries lambdaModC lambdaNModC LambdaModularPolynomialData transcendental_lambdaModC minpoly_lambdaNModC_eq"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaFieldOver lambdaModC_mem_lambdaFieldOver lambdaNModC_mem_lambdaFieldOver"
p2m_open "ModularCurve.LambdaNodeLocalized"
namespace AnhEngine

local notation "Qb" => AlgebraicClosure ℚ
local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

abbrev μ : LQ := lambdaModC Qb
abbrev μq (q : ℕ) [Fact q.Prime] : LQ := lambdaNModC Qb q

section Psi1
variable (μ' : LQ) (hμ' : Transcendental Qb μ')

theorem range_vec_μ : Set.range ![μ] = ({μ} : Set LQ) := by
  ext x; simp

theorem algInd_μ : AlgebraicIndependent Qb ![μ] :=
  algebraicIndependent_iff_transcendental.mpr (ModularCurve.transcendental_lambdaModC Qb)

include hμ' in
theorem injective_aeval_μ' : Function.Injective (MvPolynomial.aeval (R := Qb) ![μ'] : MvPolynomial (Fin 1) Qb →ₐ[Qb] LQ) :=
  algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_iff_transcendental.mpr hμ')

def ψ₁ : ↥Qb⟮μ⟯ →ₐ[Qb] LQ :=
  (IsFractionRing.liftAlgHom (K := FractionRing (MvPolynomial (Fin 1) Qb)) (injective_aeval_μ' μ' hμ')).comp
    ((algInd_μ.aevalEquivField.trans (IntermediateField.equivOfEq (by rw [range_vec_μ]))).symm.toAlgHom)

theorem ψ₁_gen : ψ₁ μ' hμ' ⟨μ, IntermediateField.mem_adjoin_simple_self Qb μ⟩ = μ' := by
  have h1 : (algInd_μ.aevalEquivField.trans (IntermediateField.equivOfEq (by rw [range_vec_μ])))
      (algebraMap (MvPolynomial (Fin 1) Qb) (FractionRing (MvPolynomial (Fin 1) Qb)) (MvPolynomial.X 0))
      = (⟨μ, IntermediateField.mem_adjoin_simple_self Qb μ⟩ : ↥Qb⟮μ⟯) := by
    apply Subtype.ext
    rw [AlgEquiv.trans_apply]
    show ((algInd_μ.aevalEquivField (algebraMap _ _ (MvPolynomial.X 0)) : ↥(IntermediateField.adjoin Qb (Set.range ![μ]))) : LQ) = μ
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe, MvPolynomial.aeval_X]
    rfl
  have h2 := (AlgEquiv.symm_apply_eq _).mpr h1.symm
  unfold ψ₁
  rw [AlgHom.comp_apply]
  change IsFractionRing.liftAlgHom _
    ((algInd_μ.aevalEquivField.trans (IntermediateField.equivOfEq _)).symm ⟨μ, _⟩) = μ'
  rw [h2, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  show MvPolynomial.aeval ![μ'] (MvPolynomial.X (0 : Fin 1)) = μ'
  rw [MvPolynomial.aeval_X]; rfl

end Psi1

section Psi2

abbrev F₁ : IntermediateField Qb LQ := Qb⟮μ⟯

abbrev μ₁ : ↥F₁ := ⟨μ, IntermediateField.mem_adjoin_simple_self Qb μ⟩

theorem minpoly_eq (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) : minpoly (↥F₁) (μq q) =
    data.Ψ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥F₁) μ₁) :=
  ModularCurve.minpoly_lambdaNModC_eq Qb q hq2 data

theorem isIntegral_μq (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) : IsIntegral (↥F₁) (μq q) := by
  by_contra h
  have h0 := minpoly.eq_zero h
  rw [minpoly_eq q hq2 data] at h0
  exact (data.monic.map _).ne_zero h0

theorem eval₂_minpoly (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q)
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) :
    (minpoly (↥F₁) (μq q)).eval₂ (ψ₁ μ' hμ').toRingHom μq' = 0 := by
  rw [minpoly_eq q hq2 data, Polynomial.eval₂_map]
  have hcomp : (ψ₁ μ' hμ').toRingHom.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥F₁) μ₁)
      = Polynomial.eval₂RingHom (Int.castRingHom LQ) μ' := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      exact ψ₁_gen μ' hμ'
  rw [hcomp]; exact hroot

def ψ₂ (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q)
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) :
    ↥(IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)) →+* LQ :=
  (AdjoinRoot.lift (ψ₁ μ' hμ').toRingHom μq' (eval₂_minpoly q hq2 data μ' μq' hμ' hroot)).comp
    (IntermediateField.adjoinRootEquivAdjoin (↥F₁) (isIntegral_μq q hq2 data)).symm.toRingEquiv.toRingHom

theorem ψ₂_algebraMap (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q)
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) (y : ↥F₁) :
    ψ₂ q hq2 data μ' μq' hμ' hroot (algebraMap (↥F₁) _ y) = ψ₁ μ' hμ' y := by
  unfold ψ₂
  rw [RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ ((IntermediateField.adjoinRootEquivAdjoin (↥F₁) _).symm (algebraMap (↥F₁) _ y)) = _
  rw [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
  rfl

theorem ψ₂_gen (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q)
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) :
    ψ₂ q hq2 data μ' μq' hμ' hroot ⟨μq q, IntermediateField.mem_adjoin_simple_self (↥F₁) (μq q)⟩ = μq' := by
  unfold ψ₂
  rw [RingHom.comp_apply]
  change AdjoinRoot.lift _ _ _ ((IntermediateField.adjoinRootEquivAdjoin (↥F₁) _).symm
    (IntermediateField.AdjoinSimple.gen (↥F₁) (μq q))) = _
  rw [IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.lift_root]

end Psi2

section Restrict

abbrev E₂ (q : ℕ) [Fact q.Prime] : Subfield LQ := (IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)).toSubfield

theorem constSeries_eq (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥K.toSubalgebra.toSubring) :
    CharPReduction.constSeries K.toSubalgebra.toSubring c = algebraMap Qb LQ (c : Qb) := rfl

theorem lambdaFieldOver_le (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : lambdaFieldOver q K ≤ E₂ q := by
  unfold lambdaFieldOver
  rw [Subfield.closure_le]
  rintro x (⟨c, rfl⟩ | rfl | rfl)
  · change CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)
    exact (IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)).algebraMap_mem (algebraMap Qb (↥F₁) (c : Qb))
  · change μ ∈ IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)
    exact (IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)).algebraMap_mem μ₁
  · change μq q ∈ IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)
    exact IntermediateField.mem_adjoin_simple_self (↥F₁) (μq q)

def incl (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(lambdaFieldOver q K) →+* ↥(IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)) where
  toFun x := ⟨x.1, lambdaFieldOver_le q K x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def τ (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) :
    ↥(lambdaFieldOver q K) →+* LQ := (ψ₂ q hq2 data μ' μq' hμ' hroot).comp (incl q K)

theorem τ_apply (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) (x : ↥(lambdaFieldOver q K)) :
    τ q hq2 data K μ' μq' hμ' hroot x = ψ₂ q hq2 data μ' μq' hμ' hroot ⟨x.1, lambdaFieldOver_le q K x.2⟩ := rfl

theorem τ_const (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) (c : ↥K.toSubalgebra.toSubring) (hc : CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ lambdaFieldOver q K) :
    τ q hq2 data K μ' μq' hμ' hroot ⟨_, hc⟩ = CharPReduction.constSeries K.toSubalgebra.toSubring c := by
  rw [τ_apply]
  have : (⟨CharPReduction.constSeries K.toSubalgebra.toSubring c, lambdaFieldOver_le q K hc⟩ :
      ↥(IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ))) = algebraMap (↥F₁) _ (algebraMap Qb ↥F₁ (c : Qb)) :=
    Subtype.ext rfl
  rw [this, ψ₂_algebraMap, AlgHom.commutes]
  rfl

theorem τ_μ (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) (h : μ ∈ lambdaFieldOver q K) : τ q hq2 data K μ' μq' hμ' hroot ⟨μ, h⟩ = μ' := by
  rw [τ_apply]
  have : (⟨μ, lambdaFieldOver_le q K h⟩ : ↥(IntermediateField.adjoin (↥F₁) ({μq q} : Set LQ)))
      = algebraMap (↥F₁) _ μ₁ := Subtype.ext rfl
  rw [this, ψ₂_algebraMap, ψ₁_gen]

theorem τ_μq (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0) (h : μq q ∈ lambdaFieldOver q K) : τ q hq2 data K μ' μq' hμ' hroot ⟨μq q, h⟩ = μq' := by
  rw [τ_apply]
  exact ψ₂_gen q hq2 data μ' μq' hμ' hroot

end Restrict

section Ext
variable (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem _root_.ModularCurve.LambdaNodeLocalized.AnhEngine.ringHom_ext {M : Type*} [DivisionRing M] (f g : ↥(lambdaFieldOver q K) →+* M)
    (hc : ∀ (c : ↥K.toSubalgebra.toSubring) (hc : CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ lambdaFieldOver q K),
      f ⟨_, hc⟩ = g ⟨_, hc⟩)
    (hμ : ∀ h : μ ∈ lambdaFieldOver q K, f ⟨μ, h⟩ = g ⟨μ, h⟩)
    (hμq : ∀ h : μq q ∈ lambdaFieldOver q K, f ⟨μq q, h⟩ = g ⟨μq q, h⟩) : f = g := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  induction hx using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | rfl | rfl
    · exact hc c _
    · exact hμ _
    · exact hμq _
  | one => change f 1 = g 1; rw [map_one, map_one]
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, add_mem hx hy⟩ : ↥(lambdaFieldOver q K)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add, map_add, ihx, ihy]
  | neg x hx ih =>
    have e : (⟨-x, neg_mem hx⟩ : ↥(lambdaFieldOver q K)) = -⟨x, hx⟩ := rfl
    rw [e, map_neg, map_neg, ih]
  | inv x hx ih =>
    have e : (⟨x⁻¹, inv_mem hx⟩ : ↥(lambdaFieldOver q K)) = (⟨x, hx⟩)⁻¹ := rfl
    rw [e, map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, mul_mem hx hy⟩ : ↥(lambdaFieldOver q K)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul, map_mul, ihx, ihy]

p2m_export "ModularCurve.LambdaNodeLocalized.AnhEngine" "ringHom_ext"

theorem map_mem (f : ↥(lambdaFieldOver q K) →+* LQ)
    (hc : ∀ (c : ↥K.toSubalgebra.toSubring) (hc : CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ lambdaFieldOver q K),
      f ⟨_, hc⟩ ∈ lambdaFieldOver q K)
    (hμ : ∀ h : μ ∈ lambdaFieldOver q K, f ⟨μ, h⟩ ∈ lambdaFieldOver q K)
    (hμq : ∀ h : μq q ∈ lambdaFieldOver q K, f ⟨μq q, h⟩ ∈ lambdaFieldOver q K)
    (x : ↥(lambdaFieldOver q K)) : f x ∈ lambdaFieldOver q K := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | rfl | rfl
    · exact hc c _
    · exact hμ _
    · exact hμq _
  | one => change f 1 ∈ lambdaFieldOver q K; rw [map_one]; exact one_mem _
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, add_mem hx hy⟩ : ↥(lambdaFieldOver q K)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add]; exact add_mem ihx ihy
  | neg x hx ih =>
    have e : (⟨-x, neg_mem hx⟩ : ↥(lambdaFieldOver q K)) = -⟨x, hx⟩ := rfl
    rw [e, map_neg]; exact neg_mem ih
  | inv x hx ih =>
    have e : (⟨x⁻¹, inv_mem hx⟩ : ↥(lambdaFieldOver q K)) = (⟨x, hx⟩)⁻¹ := rfl
    rw [e, map_inv₀]; exact inv_mem ih
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, mul_mem hx hy⟩ : ↥(lambdaFieldOver q K)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul]; exact mul_mem ihx ihy

end Ext

section Main

def σ₀ (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0)
    (hμ'F : μ' ∈ lambdaFieldOver q K) (hμq'F : μq' ∈ lambdaFieldOver q K) :
    ↥(lambdaFieldOver q K) →+* ↥(lambdaFieldOver q K) where
  toFun x := ⟨τ q hq2 data K μ' μq' hμ' hroot x,
    map_mem q K _ (fun c hc => by rw [τ_const]; exact hc)
      (fun h => by rw [τ_μ]; exact hμ'F) (fun h => by rw [τ_μq]; exact hμq'F) x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

theorem σ₀_coe (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0)
    (hμ'F : μ' ∈ lambdaFieldOver q K) (hμq'F : μq' ∈ lambdaFieldOver q K) (x : ↥(lambdaFieldOver q K)) :
    (σ₀ q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F x : LQ) = τ q hq2 data K μ' μq' hμ' hroot x := rfl

theorem σ₀_involutive (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0)
    (hμ'F : μ' ∈ lambdaFieldOver q K) (hμq'F : μq' ∈ lambdaFieldOver q K)
    (hinv : ∀ φ : ↥(lambdaFieldOver q K) →+* LQ,
      (∀ (c : ↥K.toSubalgebra.toSubring) (hc : CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ lambdaFieldOver q K),
          φ ⟨_, hc⟩ = CharPReduction.constSeries K.toSubalgebra.toSubring c) →
      φ ⟨μ, lambdaModC_mem_lambdaFieldOver q K⟩ = μ' →
      φ ⟨μq q, lambdaNModC_mem_lambdaFieldOver q K⟩ = μq' →
      φ ⟨μ', hμ'F⟩ = μ ∧ φ ⟨μq', hμq'F⟩ = μq q) : (σ₀ q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F).comp (σ₀ q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F)
    = RingHom.id _ := by
  obtain ⟨h1, h2⟩ := hinv (τ q hq2 data K μ' μq' hμ' hroot) (fun c hc => τ_const q hq2 data K μ' μq' hμ' hroot c hc)
    (τ_μ q hq2 data K μ' μq' hμ' hroot _) (τ_μq q hq2 data K μ' μq' hμ' hroot _)
  apply ringHom_ext q K
  · intro c hc
    apply Subtype.ext
    rw [RingHom.comp_apply, RingHom.id_apply, σ₀_coe]
    have e : σ₀ q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F ⟨_, hc⟩ = ⟨_, hc⟩ := Subtype.ext (τ_const q hq2 data K μ' μq' hμ' hroot c hc)
    rw [e, τ_const]
  · intro h
    apply Subtype.ext
    rw [RingHom.comp_apply, RingHom.id_apply, σ₀_coe]
    have e : σ₀ q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F ⟨μ, h⟩ = ⟨μ', hμ'F⟩ := Subtype.ext (τ_μ q hq2 data K μ' μq' hμ' hroot h)
    rw [e]; exact h1
  · intro h
    apply Subtype.ext
    rw [RingHom.comp_apply, RingHom.id_apply, σ₀_coe]
    have e : σ₀ q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F ⟨μq q, h⟩ = ⟨μq', hμq'F⟩ :=
      Subtype.ext (τ_μq q hq2 data K μ' μq' hμ' hroot h)
    rw [e]; exact h2

theorem main (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LQ) (hμ' : Transcendental Qb μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) μ') μq' = 0)
    (hμ'F : μ' ∈ lambdaFieldOver q K) (hμq'F : μq' ∈ lambdaFieldOver q K)
    (hinv : ∀ φ : ↥(lambdaFieldOver q K) →+* LQ,
      (∀ (c : ↥K.toSubalgebra.toSubring) (hc : CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ lambdaFieldOver q K),
          φ ⟨_, hc⟩ = CharPReduction.constSeries K.toSubalgebra.toSubring c) →
      φ ⟨μ, lambdaModC_mem_lambdaFieldOver q K⟩ = μ' →
      φ ⟨μq q, lambdaNModC_mem_lambdaFieldOver q K⟩ = μq' →
      φ ⟨μ', hμ'F⟩ = μ ∧ φ ⟨μq', hμq'F⟩ = μq q) : ∃ σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K),
    (∀ x : ↥(lambdaFieldOver q K), (x : LQ) ∈ Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x) ∧
    ((σ ⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LQ) = μ' ∧
    ((σ ⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LQ) = μq' := by
  set s := σ₀ q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F with hs
  have hinv' : Function.Involutive s := fun x => by
    have := congrArg (fun f => f x) (σ₀_involutive q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F hinv)
    simpa using this
  refine ⟨RingEquiv.ofBijective s hinv'.bijective, ?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨c, rfl⟩
    apply Subtype.ext
    show (s ⟨_, hx⟩ : LQ) = _
    rw [hs, σ₀_coe, τ_const]
  · show (s ⟨μ, _⟩ : LQ) = μ'
    rw [hs, σ₀_coe, τ_μ]
  · show (s ⟨μq q, _⟩ : LQ) = μq'
    rw [hs, σ₀_coe, τ_μq]

end Main

end AnhEngine
end LambdaNodeLocalized
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst.ModularCurve ModularCurve.NodeLocalized _root_.ModularCurve.LambdaNodeLocalized _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst.ModularCurve.LambdaNodeLocalized in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (μ' μq' : LaurentSeries (AlgebraicClosure ℚ)) (hμ' : Transcendental (AlgebraicClosure ℚ) μ')
    (hroot : data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) μ') μq' = 0)
    (hμ'F : μ' ∈ lambdaFieldOver q K) (hμq'F : μq' ∈ lambdaFieldOver q K)
    (hinv : ∀ φ : ↥(lambdaFieldOver q K) →+* LaurentSeries (AlgebraicClosure ℚ),
      (∀ (c : ↥K.toSubalgebra.toSubring)
          (hc : CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ lambdaFieldOver q K),
          φ ⟨_, hc⟩ = CharPReduction.constSeries K.toSubalgebra.toSubring c) →
      φ ⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ = μ' →
      φ ⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ = μq' →
      φ ⟨μ', hμ'F⟩ = lambdaModC (AlgebraicClosure ℚ) ∧ φ ⟨μq', hμq'F⟩ = lambdaNModC (AlgebraicClosure ℚ) q) :
    ∃ σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K),
      (∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
          Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x) ∧
      ((σ ⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) :
          LaurentSeries (AlgebraicClosure ℚ)) = μ' ∧
      ((σ ⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) :
          LaurentSeries (AlgebraicClosure ℚ)) = μq' :=
  ModularCurve.LambdaNodeLocalized.AnhEngine.main q hq2 data K μ' μq' hμ' hroot hμ'F hμq'F hinv

end S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst (solution)
