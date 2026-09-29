-- Prove2me | solution 1 for ModularCurve.NodeLocalized.modularRedLocHom_frickeInvolutionBar_eq_zero_iff_mem_span_branchSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/45aaca57-6db4-5040-b0ec-3f1eadd58210

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_modularRedLocHom_frickeInvolutionBar_eq_zero_iff_mem_span_branchSnd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.NodeLocalized

theorem mem_span_pair_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (σ : R ≃+* S)
    (x y g : R) : g ∈ Ideal.span {x, y} ↔ σ g ∈ Ideal.span {σ x, σ y} := by
  constructor
  · intro h
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp h
    exact Ideal.mem_span_pair.mpr ⟨σ c, σ d, by rw [← map_mul, ← map_mul, ← map_add, hcd]⟩
  · intro h
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp h
    refine Ideal.mem_span_pair.mpr ⟨σ.symm c, σ.symm d, ?_⟩
    apply σ.injective
    rw [map_add, map_mul, map_mul, σ.apply_symm_apply, σ.apply_symm_apply, hcd]

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q))
    (h₂ : ((frickeInvolutionBar (1 * q) ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : modularFunctionFieldBar (1 * q)) :
              LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ = 0 ↔
      g ∈ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
                      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} := by
  classical
  obtain ⟨σ, hσ, hσev⟩ := exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar red a ha2 K
  have ha2' : (a ^ q) ^ (q ^ 2) = a ^ q := by
    rw [← pow_mul, mul_comm, pow_mul, ha2]
  have h₁ : ((σ g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q))) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hσ g hgF]; exact h₂
  have key := modularRedLocHom_eq_zero_iff_mem_span_branchFst red (a ^ q) ha2' K ϖ hϖ (σ g) h₁
  have eπ : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩
      = CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ := by
    congr 1
    exact Subtype.ext (hσ g hgF)
  rw [eπ] at key
  rw [key]

  have e1 : σ ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩
      = ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q) _⟩ := by
    have := hσev (MvPolynomial.C ϖ)
    rw [MvPolynomial.rename_C] at this
    exact this
  have e2 : σ ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩
      = ⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (a ^ q) ((a ^ q) ^ q) _⟩ := by
    have hr : MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
        = (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q : MvPolynomial (Fin 2) ↥(coeffSubring A K)) := by
      simp only [map_sub, map_pow, MvPolynomial.rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have := hσev (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
    rw [hr] at this
    exact this
  rw [mem_span_pair_iff_of_ringEquiv σ, e1, e2]

end S_ModularCurve_NodeLocalized_modularRedLocHom_frickeInvolutionBar_eq_zero_iff_mem_span_branchSnd
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_modularRedLocHom_frickeInvolutionBar_eq_zero_iff_mem_span_branchSnd (solution)
