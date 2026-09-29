-- Prove2me | solution 1 for ModularCurve.not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9205232f-994e-5300-8a9d-43bb2e200e5c

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_Subalgebra_ringKrullDim_localization_tensor_eq_one_of_irreducible
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve
p2m_open_scoped "MatrixGroups TensorProduct Polynomial AlgebraicGeometry.Polynomial"

namespace NoIsolatedH

private theorem exists_isOpen_singleton_spec_tensor
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type) [CommRing κ] [Algebra R κ]
    (w : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))
    (hw : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base w ∈ Set.range ι.base)
    (hopen : IsOpen ({w} : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))) :
    ∃ x : ↥(Spec (CommRingCat.of (κ ⊗[R] A))), IsOpen ({x} : Set ↥(Spec (CommRingCat.of (κ ⊗[R] A)))) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)

  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]
    exact sq.w.symm
  let c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))) :=
    pullback.lift _ _ hcompat
  have hcfst : c ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) :=
    pullback.lift_snd _ _ _
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ι ≫ f) := by
    rw [hcsnd, hι]
    exact sq
  have H : IsPullback c
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (pullback.fst _ _) ι :=
    IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  haveI : IsOpenImmersion c := by rw [hc]; infer_instance
  have hrange : Set.range c.base =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base ⁻¹' Set.range ι.base := by
    rw [← Scheme.Pullback.range_fst, hc]
    ext x; constructor
    · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

  have hw' : w ∈ Set.range c.base := by rw [hrange]; exact hw
  obtain ⟨x, rfl⟩ := hw'
  refine ⟨x, ?_⟩
  have hpre : c.base ⁻¹' {c.base x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact c.isOpenEmbedding.injective.eq_iff
  rw [← hpre]
  exact hopen.preimage c.base.hom.continuous

private theorem isMaximal_and_ringKrullDim_eq_zero_of_isOpen_singleton {B : Type} [CommRing B] [IsJacobsonRing B]
    (x : ↥(Spec (CommRingCat.of B))) (hx : IsOpen ({x} : Set ↥(Spec (CommRingCat.of B)))) :
    x.asIdeal.IsMaximal ∧ ringKrullDim (Localization.AtPrime x.asIdeal) = 0 := by
  have hmin : x.asIdeal ∈ minimalPrimes B :=
    PrimeSpectrum.stableUnderGeneralization_singleton.1 hx.stableUnderGeneralization
  have hcl : IsClosed ({x} : Set ↥(Spec (CommRingCat.of B))) := by
    obtain ⟨z, hz, hzcl⟩ := nonempty_inter_closedPoints (Z := ({x} : Set ↥(Spec (CommRingCat.of B)))) ⟨x, rfl⟩
      hx.isLocallyClosed
    obtain rfl : z = x := hz
    exact mem_closedPoints_iff.mp hzcl
  have hmax : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).1 hcl
  refine ⟨hmax, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal (Localization.AtPrime x.asIdeal),
    Ideal.height_eq_zero_iff.2 hmin]
  rfl

private noncomputable def adjoinEquiv {R F : Type} [CommRing R] [Field F] [Algebra R F] (s : F) (hs : Transcendental R s) :
    R[X] ≃ₐ[R] ↥(Algebra.adjoin R ({s} : Set F)) :=
  (AlgEquiv.ofInjective (Polynomial.aeval s) ((transcendental_iff_injective).mp hs)).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval R s).symm)

private theorem transcendental_inv {R F : Type} [CommRing R] [Field F] [Algebra R F] (s : F) (hs0 : s ≠ 0)
    (hs : Transcendental R s) : Transcendental R s⁻¹ := by
  rintro ⟨q, hq0, hq⟩
  apply hs
  have hi0 : s⁻¹ ≠ 0 := inv_ne_zero hs0
  letI : Invertible s⁻¹ := invertibleOfNonzero hi0
  refine ⟨q.reverse, fun h => hq0 (Polynomial.reverse_eq_zero.mp h), ?_⟩
  have key := Polynomial.eval₂_reverse_mul_pow (algebraMap R F) s⁻¹ q
  rw [Polynomial.aeval_def] at hq
  have h2 : Polynomial.eval₂ (algebraMap R F) (⅟ s⁻¹) q.reverse = 0 := by
    rcases mul_eq_zero.mp (key.trans hq) with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ hi0)
  rwa [invOf_eq_inv, inv_inv, ← Polynomial.aeval_def] at h2

end NoIsolatedH

open NoIsolatedH in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (j : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)]
    (hj : (j : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (κ : Type) [Field κ] [CharP κ p] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ]
    (x : ↥(pullback
      (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ))))) :
    ¬ IsOpen ({x} : Set ↥(pullback
      (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ))))) := by
  classical
  intro hopen

  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  have hirr : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out
  have hk : algebraMap ↥(GaloisRep.ratLocalizedAt p) κ ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero κ p

  obtain ⟨hFTfin, hFTinf⟩ :=
    ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p Γ hT j hj
  haveI := hFTfin
  haveI := hFTinf
  haveI : Algebra.FiniteType κ (κ ⊗[↥(GaloisRep.ratLocalizedAt p)]
      ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) := inferInstance
  haveI : Algebra.FiniteType κ (κ ⊗[↥(GaloisRep.ratLocalizedAt p)]
      ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) := inferInstance
  haveI : IsJacobsonRing (κ ⊗[↥(GaloisRep.ratLocalizedAt p)]
      ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) := isJacobsonRing_of_finiteType (A := κ)
  haveI : IsJacobsonRing (κ ⊗[↥(GaloisRep.ratLocalizedAt p)]
      ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) := isJacobsonRing_of_finiteType (A := κ)

  have hjq : (j : LaurentSeries ℚ) = coeffEmb ℚ jq := by
    rw [hj]
    show jq = coeffMap (algebraMap ℚ ℚ) jq
    ext k
    rw [coeffMap_coeff, Algebra.algebraMap_self, RingHom.id_apply]
  have hIST : @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ)).toSMul _ :=
    @IsScalarTower.of_algebraMap_eq' ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ)) _
      (RingHom.ext fun r => by
        show ((r : ℚ) : ↥(qExpFunctionFieldC ℚ Γ)) =
          @algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) _ _ (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ Γ)) (r : ℚ)
        exact (eq_ratCast _ _).symm)
  have htj : Transcendental ↥(GaloisRep.ratLocalizedAt p) (j : ↥(qExpFunctionFieldC ℚ Γ)) :=
    @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ Γ) ↥(GaloisRep.ratLocalizedAt p) _ _ _ _
      _ hIST j hjq
  have htj' : Transcendental ↥(GaloisRep.ratLocalizedAt p) (j : ↥(qExpFunctionFieldC ℚ Γ))⁻¹ :=
    transcendental_inv _ (Fact.out) htj

  rcases mem_range_ιFin_or_mem_range_ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j
      ((pullback.fst (toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ)))).base x) with hfin | hinf
  · obtain ⟨y, hy⟩ := exists_isOpen_singleton_spec_tensor (toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (ιFin_toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) κ x hfin hopen
    obtain ⟨hmax, h0⟩ := isMaximal_and_ringKrullDim_eq_zero_of_isOpen_singleton y hy
    haveI := hmax
    have h1 := Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hirr
      (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({(j : ↥(qExpFunctionFieldC ℚ Γ))} : Set ↥(qExpFunctionFieldC ℚ Γ)))
      (chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (adjoinEquiv _ htj) (adjoin_le_chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _)
      (fun a => a.2) hFTfin (isIntegrallyClosed_chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _) κ hk
      y.asIdeal
    rw [h0] at h1
    exact zero_ne_one h1
  · obtain ⟨y, hy⟩ := exists_isOpen_singleton_spec_tensor (toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (ιInf_toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) κ x hinf hopen
    obtain ⟨hmax, h0⟩ := isMaximal_and_ringKrullDim_eq_zero_of_isOpen_singleton y hy
    haveI := hmax
    have h1 := Subalgebra.ringKrullDim_localization_tensor_eq_one_of_irreducible hirr
      (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({(j : ↥(qExpFunctionFieldC ℚ Γ))⁻¹} : Set ↥(qExpFunctionFieldC ℚ Γ)))
      (chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (adjoinEquiv _ htj') (adjoin_le_chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _)
      (fun a => a.2) hFTinf (isIntegrallyClosed_chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) _) κ hk
      y.asIdeal
    rw [h0] at h1
    exact zero_ne_one h1

end S_ModularCurve_not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP
end P2MW
export P2MW.S_ModularCurve_not_isOpen_singleton_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charP (solution)
