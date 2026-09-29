-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.spPic0_heckeGen_ell_eq_heckeFibreGeom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4cd7813b-beff-5f08-961f-ad269575b170

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_spPic0_heckeGen_ell_eq_heckeFibreGeom
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

theorem solution
    (N : ℕ) [NeZero N] (hcomm : HeckeOperatorsCommuteBar N)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    [IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)]
    (S : PlaceSpecialization A ℓ N data hKr (ResidueField ↥A)
        (IsLocalRing.residue ↥A) hα hβ) :
    letI := heckeModuleBar N
    ∀ x : JZero N,
      (heckeFibreGeomLevelPic0OfIsCurveOver
          (ResidueField ↥A) N data hKr).toIntLinearMap (S.spPic0 x)
        = S.spPic0 (heckeGen ⟨ℓ, hℓ.out⟩ • x) := by
  letI := heckeModuleBar N
  set k := ResidueField ↥A
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI : NeZero (N * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne N) hℓ.out.ne_zero⟩

  obtain ⟨_, _, hP, hfin, hFI, hN⟩ :=
    ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) N ℓ
  haveI := hP

  have key : ∀ v,
      Finsupp.mapDomain S.sp (heckeDivBar hα hβ (Finsupp.single v 1))
        = heckeFibreGeomLevel k N data hKr (Finsupp.single (S.sp v) 1) := fun v =>
    ModularCurve.mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel
      N ℓ hℓN hα hβ (deg_eq_one_modularFunctionFieldBar (N * ℓ))
      data hKr S.sp S.d1 S.d2 v
  have hdiv_hom :
      (Finsupp.mapDomain.addMonoidHom S.sp).comp (heckeDivBar hα hβ)
        = (heckeFibreGeomLevel k N data hKr).comp
            (Finsupp.mapDomain.addMonoidHom S.sp) := by
    refine Finsupp.addHom_ext' fun v => AddMonoidHom.ext_int ?_
    simpa using key v
  have hdiv : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Finsupp.mapDomain S.sp (heckeDivBar hα hβ D)
        = heckeFibreGeomLevel k N data hKr (Finsupp.mapDomain S.sp D) :=
    fun D => DFunLike.congr_fun hdiv_hom D

  intro x

  have hop : (letI := heckeModuleBar N; heckeGen ⟨ℓ, hℓ.out⟩ • x)
      = heckePic0Bar hα hβ hFI hfin hN x := by
    rw [heckeModuleBar_heckeGen_smul hcomm ⟨ℓ, hℓ.out⟩ x, heckeOperatorBar_apply]
    exact DFunLike.congr_fun (heckeOperatorAlong_eq hα hβ hFI hfin hN) x
  rw [hop]

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x

  obtain ⟨D', hD'_coe, hD'_mk⟩ := S.spPic0_compat D

  rw [hD'_mk]
  show heckeFibreGeomLevelPic0OfIsCurveOver k N data hKr (Pic0.mk D')
      = S.spPic0 (heckePic0Bar hα hβ hFI hfin hN (Pic0.mk D))
  rw [heckeFibreGeomLevelPic0OfIsCurveOver_mk]

  have hmk :
      heckePic0Bar hα hβ hFI hfin hN (Pic0.mk D)
        = Pic0.mk (Pic0.degZeroCorrespondence
            (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
            (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hβ hα hFI D) :=
    Pic0.correspondence_mk _ _ _ _ _ _ _ D
  rw [hmk]
  obtain ⟨Dh', hDh'_coe, hDh'_mk⟩ :=
    S.spPic0_compat (Pic0.degZeroCorrespondence
      (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hβ hα hFI D)
  rw [hDh'_mk]

  congr 1
  refine Subtype.ext ?_
  rw [coe_heckeFibreGeomLevelDegZero, hD'_coe, hDh'_coe,
    Pic0.coe_degZeroCorrespondence]
  exact (hdiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))).symm

end S_ModularCurve_PlaceSpecialization_spPic0_heckeGen_ell_eq_heckeFibreGeom
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_spPic0_heckeGen_ell_eq_heckeFibreGeom (solution)
