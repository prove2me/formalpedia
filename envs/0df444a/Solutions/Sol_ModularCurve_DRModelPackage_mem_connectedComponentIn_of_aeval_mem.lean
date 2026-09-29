-- Prove2me | solution 1 for ModularCurve.DRModelPackage.mem_connectedComponentIn_of_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1843e07b-0901-57ee-8049-6c67ca593d89

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_ModularCurve_DRModelPackage_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
import Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_toBase_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_mem_connectedComponentIn_of_aeval_mem
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec"
p2m_attr_erase "simp" "GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_mem_connectedComponentIn_of_aeval_mem.ModularCurve AlgebraicCurve AlgebraicGeometry.RelPicard"
open AlgebraicGeometry.SmoothProperCurve
open ModularCurve.DRModelPackage

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage modularFunctionFieldFull IgusaScheme.jFull IgusaScheme HpoolLevelRing.Afin DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf IgusaScheme.geometricallyConnected_toBase_int"
namespace ZCompAux
p2m_open "ModularCurve"

variable (p : ℕ) [Fact p.Prime]

theorem mem_smoothLocus_of_not_mem (𝔛 : DRModelPackage p) (x : ↥(DRModel p))
    (hx : ((DRModel.toBase p).base x) ∈ PrimeSpectrum.basicOpen (p : ℤ)) : x ∈ 𝔛.smoothLocus := by

  let ιp : Spec (CommRingCat.of (Localization.Away (p : ℤ))) ⟶ Spec (CommRingCat.of ℤ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))
  haveI : IsOpenImmersion ιp := IsOpenImmersion.of_isLocalization (p : ℤ)
  let g := pullback.fst (DRModel.toBase p) ιp
  let U : (DRModel p).Opens := Scheme.Hom.opensRange g
  have hsm : Smooth (U.ι ≫ DRModel.toBase p) := by

    haveI : Smooth (pullback.snd (DRModel.toBase p) ιp) := 𝔛.smooth_away
    have hU : U.ι = (Scheme.Hom.isoOpensRange g).inv ≫ g :=
      (Iso.eq_inv_comp _).mpr (Scheme.Hom.isoOpensRange_hom_ι g)
    have hfac : U.ι ≫ DRModel.toBase p = (Scheme.Hom.isoOpensRange g).inv ≫ pullback.snd (DRModel.toBase p) ιp ≫ ιp := by
      rw [hU, Category.assoc]
      congr 1
      exact pullback.condition
    rw [hfac]
    infer_instance
  have hU : U ≤ 𝔛.smoothLocus := 𝔛.smoothLocus_maximal U hsm
  apply hU

  show x ∈ Set.range g.base
  rw [Scheme.Pullback.range_fst]
  show (DRModel.toBase p).base x ∈ Set.range ιp.base
  have : Set.range ιp.base = (PrimeSpectrum.basicOpen (p : ℤ) : Set (PrimeSpectrum ℤ)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away (p : ℤ)) (p : ℤ)
  rw [this]
  exact hx

omit [Fact p.Prime] in

theorem specMap_point_mem_basicOpen (k : Type) [Field k] (hk : (p : k) ≠ 0)
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)) (t : ↥(Spec (CommRingCat.of k))) :
    s.base t ∈ PrimeSpectrum.basicOpen (p : ℤ) := by
  rw [← Spec.map_preimage s]
  show (p : ℤ) ∉ (PrimeSpectrum.comap (Spec.preimage s).hom t).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, eq_intCast]
  intro h
  apply hk
  have : t.asIdeal = ⊥ := by
    haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
    rw [Subsingleton.elim t (⊥ : PrimeSpectrum k)]
    rfl
  rw [this] at h
  simpa using h

end ModularCurve.ZCompAux

open ModularCurve.ZCompAux in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (v : HpoolLevelRing.Afin p)
    (hdict : ∀ (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
      (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
      (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p)),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y =
        (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 →
      v ∉ 𝔮.asIdeal →
      y ∈ Set.range (𝔛.compInf k).base ∧ y ∉ Set.range (𝔛.compZero k).base)
    (g : Polynomial ℤ) (hg0 : ¬ (p : ℤ) ∣ g.coeff 0) (f : ℤ)
    (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
    (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p))
    (hy : (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫
        pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base y =
      (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮)
    (hg : Polynomial.aeval v g ∈ 𝔮.asIdeal) :
    y ∈ connectedComponentIn
      (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
      (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) := by
  classical
  have hp : p.Prime := Fact.out
  set L := Localization.Away f with hL
  set g₂ := pullback.fst (baseChange ℤ (DRModel.toBase p) L) s ≫
    pullback.fst (DRModel.toBase p) (specMap ℤ L) with hg₂
  set x₀ := ((sectionFibrePoint (sectionBaseChange L 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k) with hx₀

  have hs : s ≫ specMap ℤ L = specMap ℤ k := specZIsTerminal.hom_ext _ _

  have hfac : g₂ ≫ DRModel.toBase p = pullback.snd (baseChange ℤ (DRModel.toBase p) L) s ≫ specMap ℤ k := by
    rw [hg₂, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hs]
  have hbase : ∀ z, (DRModel.toBase p).base (g₂.base z) =
      (specMap ℤ k).base ((pullback.snd (baseChange ℤ (DRModel.toBase p) L) s).base z) := by
    intro z
    change (g₂ ≫ DRModel.toBase p).base z = (pullback.snd _ s ≫ specMap ℤ k).base z
    rw [hfac]

  by_cases hpk : (p : k) = 0
  swap
  ·

    have hall : ∀ z, g₂.base z ∈ 𝔛.smoothLocus := by
      intro z
      apply mem_smoothLocus_of_not_mem p 𝔛
      rw [hbase]
      exact specMap_point_mem_basicOpen p k hpk (specMap ℤ k) _
    have htop : ((g₂ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (baseChange ℤ (DRModel.toBase p) L) s).Opens) :
        Set ↥(pullback (baseChange ℤ (DRModel.toBase p) L) s)) = Set.univ :=
      Set.eq_univ_of_forall fun z => hall z
    show y ∈ connectedComponentIn ((g₂ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (baseChange ℤ (DRModel.toBase p) L) s).Opens) : Set _) x₀
    rw [htop, connectedComponentIn_univ]
    haveI : GeometricallyConnected (DRModel.toBase p) := ModularCurve.IgusaScheme.geometricallyConnected_toBase_int p
    haveI : ConnectedSpace ↥(pullback (baseChange ℤ (DRModel.toBase p) L) s) :=
      GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (baseChange ℤ (DRModel.toBase p) L) s)
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.mem_univ y

  haveI hchar : CharP k p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp hpk)

  have hker : 𝔮.asIdeal.comap (algebraMap ℤ (HpoolLevelRing.Afin p)) = RingHom.ker (algebraMap ℤ k) := by
    have h1 : ((DRModel.toBase p).base (g₂.base y)).asIdeal = 𝔮.asIdeal.comap (algebraMap ℤ (HpoolLevelRing.Afin p)) := by
      have hy' : g₂.base y = (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 := hy
      rw [hy']
      change ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ≫ DRModel.toBase p).base 𝔮).asIdeal = _
      erw [TwoChartIntegralModel.ιFin_toBase]
      rw [Spec.map_base]
      rfl
    have h2 : ((DRModel.toBase p).base (g₂.base y)).asIdeal = RingHom.ker (algebraMap ℤ k) := by
      rw [hbase, Spec.map_base]
      set t := (pullback.snd (baseChange ℤ (DRModel.toBase p) L) s).base y with ht
      have htb : t.asIdeal = ⊥ := by
        haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
        rw [Subsingleton.elim t (⊥ : PrimeSpectrum k)]; rfl
      change (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap ℤ k)).hom t).asIdeal = _
      rw [PrimeSpectrum.comap_asIdeal, htb, ← RingHom.ker_eq_comap_bot]
      rfl
    rw [← h1, h2]
  have hp𝔮 : (p : HpoolLevelRing.Afin p) ∈ 𝔮.asIdeal := by
    have : (p : ℤ) ∈ 𝔮.asIdeal.comap (algebraMap ℤ (HpoolLevelRing.Afin p)) := by
      rw [hker, RingHom.mem_ker, map_natCast]; exact hpk
    simpa [Ideal.mem_comap] using this

  have hv : v ∉ 𝔮.asIdeal := by
    intro hvq
    obtain ⟨h, hh⟩ := (Polynomial.X_dvd_sub_C (p := g))
    have h1 : Polynomial.aeval v g - algebraMap ℤ (HpoolLevelRing.Afin p) (g.coeff 0) ∈ 𝔮.asIdeal := by
      have e : Polynomial.aeval v g - algebraMap ℤ (HpoolLevelRing.Afin p) (g.coeff 0) = v * Polynomial.aeval v h := by
        have := congrArg (Polynomial.aeval v) hh
        rw [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X] at this
        exact this
      rw [e]; exact 𝔮.asIdeal.mul_mem_right _ hvq
    have h2 : algebraMap ℤ (HpoolLevelRing.Afin p) (g.coeff 0) ∈ 𝔮.asIdeal := by
      have := 𝔮.asIdeal.sub_mem hg h1
      rwa [sub_sub_cancel] at this
    have h3 : (g.coeff 0 : ℤ) ∈ RingHom.ker (algebraMap ℤ k) := by rw [← hker]; exact h2
    rw [RingHom.mem_ker, eq_intCast, CharP.intCast_eq_zero_iff k p] at h3
    exact hg0 h3

  let e₁ : pullback (baseChange ℤ (DRModel.toBase p) L) s ≅ pullback (DRModel.toBase p) (s ≫ specMap ℤ L) :=
    pullbackLeftPullbackSndIso (DRModel.toBase p) (specMap ℤ L) s
  let e₂ : pullback (DRModel.toBase p) (s ≫ specMap ℤ L) ≅ pullback (DRModel.toBase p) (specMap ℤ k) :=
    pullback.congrHom rfl hs
  let e : pullback (baseChange ℤ (DRModel.toBase p) L) s ≅ pullback (DRModel.toBase p) (specMap ℤ k) := e₁ ≪≫ e₂
  have he₂_fst : e₂.hom ≫ pullback.fst (DRModel.toBase p) (specMap ℤ k) = pullback.fst _ _ := by
    rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have he₂_snd : e₂.hom ≫ pullback.snd (DRModel.toBase p) (specMap ℤ k) = pullback.snd _ _ := by
    rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  have he_fst : e.hom ≫ pullback.fst (DRModel.toBase p) (specMap ℤ k) = g₂ := by
    show (e₁.hom ≫ e₂.hom) ≫ _ = _
    rw [Category.assoc, he₂_fst, pullbackLeftPullbackSndIso_hom_fst]
  have he_snd : e.hom ≫ pullback.snd (DRModel.toBase p) (specMap ℤ k) = pullback.snd _ s := by
    show (e₁.hom ≫ e₂.hom) ≫ _ = _
    rw [Category.assoc, he₂_snd, pullbackLeftPullbackSndIso_hom_snd]

  set y' : ↥(pullback (DRModel.toBase p) (specMap ℤ k)) := e.hom.base y with hy'
  have hfst' : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y' =
      (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 := by
    rw [hy']
    change (e.hom ≫ pullback.fst (DRModel.toBase p) (specMap ℤ k)).base y = _
    rw [he_fst]
    exact hy
  obtain ⟨hInf, hZero⟩ := hdict k y' 𝔮 hfst' hv
  have hC := (ModularCurve.DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
    p 𝔛 k y' hInf hZero).2

  let φ : ↥(pullback (baseChange ℤ (DRModel.toBase p) L) s) ≃ₜ ↥(pullback (DRModel.toBase p) (specMap ℤ k)) :=
    Scheme.homeoOfIso e
  have hφ : ∀ z, φ z = e.hom.base z := fun z => rfl

  have hF : (φ : _ → _) '' (((g₂ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (baseChange ℤ (DRModel.toBase p) L) s).Opens) : Set _))
      = ((pullback.fst (DRModel.toBase p) (specMap ℤ k) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (DRModel.toBase p) (specMap ℤ k)).Opens) : Set _) := by
    have hpre : (((g₂ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (baseChange ℤ (DRModel.toBase p) L) s).Opens) : Set _))
        = φ ⁻¹' ((pullback.fst (DRModel.toBase p) (specMap ℤ k) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (DRModel.toBase p) (specMap ℤ k)).Opens) : Set _) := by
      ext z
      simp only [Set.mem_preimage, hφ]
      change g₂.base z ∈ (𝔛.smoothLocus : Set _) ↔ (pullback.fst (DRModel.toBase p) (specMap ℤ k)).base (e.hom.base z) ∈ (𝔛.smoothLocus : Set _)
      rw [← he_fst]
      rfl
    rw [hpre, Homeomorph.image_preimage]

  have hcomp : (sectionFibrePoint (sectionBaseChange L 𝔛.εinf) s).1 ≫ g₂ = (s ≫ specMap ℤ L) ≫ 𝔛.εinf.1 := by
    rw [hg₂, ← Category.assoc]
    show (pullback.lift (s ≫ (sectionBaseChange L 𝔛.εinf).1) (𝟙 _) _ ≫ _) ≫ _ = _
    rw [pullback.lift_fst, Category.assoc, sectionBaseChange_coe_fst, Category.assoc]

  have hmor : (sectionFibrePoint (sectionBaseChange L 𝔛.εinf) s).1 ≫ e.hom =
      (sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, he_fst, hcomp, hs]
      show _ = pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) ≫ 𝔛.εinf.1) (𝟙 _) _ ≫ _
      rw [pullback.lift_fst]
    · rw [Category.assoc, he_snd, (sectionFibrePoint (sectionBaseChange L 𝔛.εinf) s).2,
        (sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).2]
  have hx : φ x₀ = ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k) := by
    rw [hφ, hx₀]
    change ((sectionFibrePoint (sectionBaseChange L 𝔛.εinf) s).1 ≫ e.hom).base (IsLocalRing.closedPoint k) = _
    rw [hmor]

  have hx₀F : x₀ ∈ (((g₂ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (baseChange ℤ (DRModel.toBase p) L) s).Opens) : Set _)) := by
    show g₂.base x₀ ∈ (𝔛.smoothLocus : Set ↥(DRModel p))
    rw [hx₀]
    change ((sectionFibrePoint (sectionBaseChange L 𝔛.εinf) s).1 ≫ g₂).base (IsLocalRing.closedPoint k) ∈ _
    rw [hcomp]
    exact 𝔛.εinf_mem_smoothLocus ⟨_, rfl⟩

  have himg := Homeomorph.image_connectedComponentIn φ hx₀F
  rw [hF, hx] at himg
  have : φ y ∈ (φ : _ → _) '' connectedComponentIn
      (((g₂ ⁻¹ᵁ 𝔛.smoothLocus : (pullback (baseChange ℤ (DRModel.toBase p) L) s).Opens) : Set _)) x₀ := by
    rw [himg]; exact hC
  exact (φ.injective.mem_set_image).1 this

end S_ModularCurve_DRModelPackage_mem_connectedComponentIn_of_aeval_mem
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_mem_connectedComponentIn_of_aeval_mem (solution)
