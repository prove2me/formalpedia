-- Prove2me | solution 1 for ModularCurve.isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7eb312fc-3ee9-5659-b198-4eff04264715

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicGeometry_locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_fibre_mul_comm
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite
import Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_pow_char
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor"
p2m_attr_erase "instance" "AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve

namespace FinJ0Glue

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem fibre_nsmul (L : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{0}))
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (RelativeGroupLaw.baseResidueField s)))
    (n : ℕ) (x : SchemeHomOver t' (RelativeGroupLaw.fibreStr f s)) :
    RelativeGroupLaw.fibrePointToBase s ((L.fibre s).nsmul t' n x) =
      L.nsmul _ n (RelativeGroupLaw.fibrePointToBase s x) := by
  induction n with
  | zero => simp [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.fibre_one]
  | succ n ih => simp [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.fibre_mul, ih]

theorem finite_torsionSubset_fibre_iff (L : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{0}))
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (RelativeGroupLaw.baseResidueField s))) (n : ℕ) :
    ((L.fibre s).torsionSubset t' n).Finite ↔
      (L.torsionSubset (t' ≫ RelativeGroupLaw.basePointInclusion s) n).Finite := by
  have himage : (RelativeGroupLaw.fibrePointEquiv s t') '' ((L.fibre s).torsionSubset t' n) =
      L.torsionSubset (t' ≫ RelativeGroupLaw.basePointInclusion s) n := by
    ext y
    simp only [Set.mem_image, RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show L.nsmul _ n (RelativeGroupLaw.fibrePointToBase s x) = L.one _
      rw [← fibre_nsmul, hx, RelativeGroupLaw.fibre_one, RelativeGroupLaw.fibrePointToBase_ofBase]
    · intro hy
      refine ⟨(RelativeGroupLaw.fibrePointEquiv s t').symm y, ?_, Equiv.apply_symm_apply _ _⟩
      apply (RelativeGroupLaw.fibrePointEquiv s t').injective
      show RelativeGroupLaw.fibrePointToBase s ((L.fibre s).nsmul t' n _) = RelativeGroupLaw.fibrePointToBase s _
      rw [fibre_nsmul, RelativeGroupLaw.fibre_one, RelativeGroupLaw.fibrePointToBase_ofBase]
      show L.nsmul _ n (RelativeGroupLaw.fibrePointEquiv s t' ((RelativeGroupLaw.fibrePointEquiv s t').symm y)) = _
      rw [Equiv.apply_symm_apply]; exact hy
  rw [← himage]
  exact (Set.finite_image_iff (RelativeGroupLaw.fibrePointEquiv s t').injective.injOn).symm

theorem pts_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    {G : Type} [AddCommGroup G] (pts : G ≃ SchemeHomOver t f)
    (hadd : ∀ u v : G, pts (u + v) = L.mul t (pts u) (pts v)) (n : ℕ) (u : G) :
    pts (n • u) = L.nsmul t n (pts u) := by
  have h0 : pts 0 = L.one t := by
    have h1 := hadd 0 0
    rw [add_zero] at h1
    have := congrArg (fun z => L.mul t (L.inv t (pts 0)) z) h1
    beta_reduce at this
    rwa [L.inv_mul_cancel, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul, eq_comm] at this
  induction n with
  | zero => rw [zero_smul, h0, RelativeGroupLaw.nsmul_zero]
  | succ n ih => rw [succ_nsmul, hadd, ih, RelativeGroupLaw.nsmul_succ]

theorem torsionSubset_finite_of_equiv (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    {G : Type} [AddCommGroup G] (pts : G ≃ SchemeHomOver t f)
    (hadd : ∀ u v : G, pts (u + v) = L.mul t (pts u) (pts v)) (n : ℕ)
    (hfin : {u : G | n • u = 0}.Finite) : (L.torsionSubset t n).Finite := by
  have h0 : pts 0 = L.one t := by
    have := pts_nsmul L t pts hadd 0 0
    rwa [zero_smul, RelativeGroupLaw.nsmul_zero] at this
  refine (hfin.image pts).subset ?_
  intro x hx
  refine ⟨pts.symm x, ?_, pts.apply_symm_apply x⟩
  show n • pts.symm x = 0
  apply pts.injective
  rw [pts_nsmul L t pts hadd, pts.apply_symm_apply, h0]
  exact hx

end FinJ0Glue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hJ : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (ptsSp : JZeroC (ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f)
    (hadd : ∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v))
    (k : ℕ) :
    IsFinite (L.schemeNsmul (ℓ ^ k)) ∧ Flat (L.schemeNsmul (ℓ ^ k)) := by
  haveI hdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt ℓ) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt ℓ Fact.out
  haveI : IsNoetherianRing ↥(GaloisRep.ratLocalizedAt ℓ) := inferInstance
  have hn : 0 < ℓ ^ k := pow_pos (Fact.out : ℓ.Prime).pos k
  haveI : IsProper f := hJ.proper

  have hlqf : LocallyQuasiFinite (L.schemeNsmul (ℓ ^ k)) := by
    refine AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo f
      (L.schemeNsmul (ℓ ^ k)) (L.schemeNsmul_over (ℓ ^ k)) ?_
    intro s
    rw [← RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo L s (ℓ ^ k)]
    have hfib := GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr hJ s
    haveI : Smooth (RelativeGroupLaw.fibreStr f s) := hfib.smooth
    haveI : LocallyOfFiniteType (RelativeGroupLaw.fibreStr f s) := inferInstance
    by_cases hu : IsUnit ((ℓ ^ k : ℕ) : RelativeGroupLaw.baseResidueField s)
    · exact RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit (L.fibre s)
        (fun t' x y => RelativeGroupLaw.fibre_mul_comm L hcomm s t' x y) (ℓ ^ k) hu
    ·
      have hk : k ≠ 0 := by rintro rfl; exact hu (by simp)
      have hℓ0 : ((ℓ : ℕ) : RelativeGroupLaw.baseResidueField s) = 0 := by
        by_contra hne
        apply hu
        rw [Nat.cast_pow]
        exact (IsUnit.mk0 _ hne).pow k

      have hmax : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt ℓ) =
          Ideal.span {((ℓ : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ))} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
          (GaloisRep.irreducible_natCast_ratLocalizedAt ℓ Fact.out)
      have hmem : ((ℓ : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ)) ∈ s.asIdeal := by
        have hev : ((Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))).Γevaluation s)
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))).inv
              ((ℓ : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ))) = 0 := by
          rw [map_natCast, map_natCast]; exact hℓ0
        have h2 := (@Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ ⊤ s trivial _).mp hev
        rw [basicOpen_eq_of_affine] at h2
        by_contra hn
        exact h2 ((PrimeSpectrum.mem_basicOpen _ _).mpr hn)
      have hs : s = IsLocalRing.closedPoint ↥(GaloisRep.ratLocalizedAt ℓ) := by
        apply PrimeSpectrum.ext
        have hle : IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt ℓ) ≤ s.asIdeal := by
          rw [hmax]; exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
        exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le s.isPrime.ne_top hle).symm

      haveI hcharA : CharP (ResidueField ↥A) ℓ := A.residueField_charP_of_liesOverPrime Fact.out hA
      have hpt : (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) (IsLocalRing.closedPoint (ResidueField ↥A)) = s := by
        rw [hs]
        obtain ⟨ρ', hρ'⟩ := Spec.map_surjective (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA)
        haveI : IsLocalHom ρ'.hom := by
          refine ⟨fun a ha => ?_⟩
          by_contra hna
          have hamem : a ∈ IsLocalRing.maximalIdeal ↥(GaloisRep.ratLocalizedAt ℓ) := hna
          rw [hmax, Ideal.mem_span_singleton] at hamem
          obtain ⟨b, rfl⟩ := hamem
          rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul] at ha
          exact not_isUnit_zero ha
        rw [← hρ']
        exact Spec_closedPoint

      have hfac : (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) = Spec.map (Scheme.SpecToEquivOfField _ _ (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA)).2 ≫
          (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))).fromSpecResidueField
            (Scheme.SpecToEquivOfField _ _ (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA)).1 :=
        ((Scheme.SpecToEquivOfField _ _).symm_apply_apply (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA)).symm
      have h1 : (Scheme.SpecToEquivOfField _ _ (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA)).1 = s := hpt
      generalize hq : Scheme.SpecToEquivOfField (ResidueField ↥A)
        (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) = q at hfac h1
      obtain ⟨s', φ⟩ := q
      dsimp only at h1 hfac
      subst h1
      letI : Algebra (RelativeGroupLaw.baseResidueField s') (ResidueField ↥A) := φ.hom.toAlgebra
      haveI : IsAlgClosed (ResidueField ↥A) := A.isAlgClosed_residueField_algebraicClosure_rat
      refine RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_finite_torsionSubset (L.fibre s')
        (fun t' x y => RelativeGroupLaw.fibre_mul_comm L hcomm s' t' x y) (ResidueField ↥A) (ℓ ^ k) ?_
      have hφ : CommRingCat.ofHom (algebraMap (RelativeGroupLaw.baseResidueField s') (ResidueField ↥A)) = φ := rfl
      rw [hφ, FinJ0Glue.finite_torsionSubset_fibre_iff, show Spec.map φ ≫ RelativeGroupLaw.basePointInclusion s' = (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA)
        from hfac.symm]

      refine FinJ0Glue.torsionSubset_finite_of_equiv L (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) ptsSp hadd (ℓ ^ k) ?_
      haveI : PerfectField (ResidueField ↥A) := inferInstance
      haveI hco := ModularCurve.isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) p
      haveI hef := ModularCurve.essFiniteType_modularFunctionFieldFullC (ResidueField ↥A) p
      haveI := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := ResidueField ↥A)
        (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) p))
      have hfg : ∃ x : ↥(modularFunctionFieldFullC (ResidueField ↥A) p), Transcendental (ResidueField ↥A) x ∧
          FiniteDimensional (IntermediateField.adjoin (ResidueField ↥A) ({x} : Set _)) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) ∧
          Algebra.IsSeparable (IntermediateField.adjoin (ResidueField ↥A) ({x} : Set _)) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) := by
        obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
        have hsep := ModularCurve.isSeparable_jqNModC_of_good (ResidueField ↥A) p ℓ hℓp
        have hC : ∃ x : ↥(modularFunctionFieldC (ResidueField ↥A) p), Transcendental (ResidueField ↥A) x ∧
            FiniteDimensional (IntermediateField.adjoin (ResidueField ↥A) ({x} : Set _)) ↥(modularFunctionFieldC (ResidueField ↥A) p) ∧
            Algebra.IsSeparable (IntermediateField.adjoin (ResidueField ↥A) ({x} : Set _)) ↥(modularFunctionFieldC (ResidueField ↥A) p) := by
          have hfs := ModularCurve.finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
            (ResidueField ↥A) p data hsep
          refine ⟨⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) p⟩, ?_, hfs.1, hfs.2⟩
          have ht := ModularCurve.transcendental_jqNModC (ResidueField ↥A) 1
          rw [jqNModC_one] at ht
          exact (transcendental_algebraMap_iff
            (algebraMap (↥(modularFunctionFieldC (ResidueField ↥A) p)) (LaurentSeries (ResidueField ↥A))).injective).mp ht
        rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) ℓ p hℓp] at hC
        exact hC
      have hT := AlgebraicCurve.Pic0.finite_torsion_pow_char (ResidueField ↥A)
        ↥(modularFunctionFieldFullC (ResidueField ↥A) p) ℓ hfg k
      rw [← Set.finite_coe_iff]
      refine Finite.of_equiv _ (Equiv.subtypeEquivRight ?_ : ↥(Pic0.torsion (ResidueField ↥A) _ (ℓ ^ k)) ≃ _)
      intro u
      rw [Pic0.mem_torsion, Set.mem_setOf_eq, Nat.cast_pow, ← natCast_zsmul, Nat.cast_pow]
  haveI := hlqf
  haveI : IsProper (L.schemeNsmul (ℓ ^ k)) := by
    have : IsProper (L.schemeNsmul (ℓ ^ k) ≫ f) := by rw [L.schemeNsmul_over]; infer_instance
    exact IsProper.of_comp _ f
  have hfin : IsFinite (L.schemeNsmul (ℓ ^ k)) := IsFinite.of_isProper_of_locallyQuasiFinite _
  exact ⟨hfin, RelativeGroupLaw.flat_schemeNsmul_of_isFinite L hJ (fun t x y => hcomm t x y) (ℓ ^ k) hn hfin⟩

end S_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points
end P2MW
export P2MW.S_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points (solution)
