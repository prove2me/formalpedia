-- Prove2me | solution 1 for ModularCurve.DRModel.exists_ne_and_notMem_chartFin_pFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b2545da6-61d7-5f36-bb70-aebcd6765e77

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_int_chartAlgInf_eq_coeff_zero
import Theorems.Thm_ModularCurve_DRModel_dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime
import Theorems.Thm_ModularCurve_DRModel_exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve AlgebraicCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage jq coeff_jq_neg_one coeff_jq_of_lt jq_ne_zero modularFunctionFieldFull IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme DRModel.exists_chartAlgFin_valuationSubring_pair_levelP IgusaScheme.exists_algHom_int_chartAlgInf_eq_coeff_zero DRModel.dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime DRModel.exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive"
namespace DRModel
p2m_export "ModularCurve.DRModel" "toBase exists_chartAlgFin_valuationSubring_pair_levelP dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive"
namespace Cusps2
p2m_open "ModularCurve.DRModel ModularCurve"

universe u

theorem pushout_inl_eq_inr_iff {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] (x : X) (y : Y) :
    (pushout.inl f g).base x = (pushout.inr f g).base y ↔
      ∃ w : U, f.base w = x ∧ g.base w = y := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span f g)
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x) (xj := y)).mp h
    rcases k with (_ | _ | _)
    · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      subst hfi hfj
      exact ⟨w, by simp at h₁; exact h₁, by simp at h₂; exact h₂⟩
    · change WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) at fj
      rcases fj with ⟨⟩
    · change WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) at fi
      rcases fi with ⟨⟩
  · rintro ⟨w, rfl, rfl⟩
    change (f ≫ pushout.inl f g).base w = (g ≫ pushout.inr f g).base w
    rw [pushout.condition]

section TwoChart

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem range_fInf_base : Set.range (TwoChartIntegralModel.fInf R F j).base =
    ((PrimeSpectrum.basicOpen (TwoChartIntegralModel.jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j))) :
      Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf R F j))) := by
  letI := (TwoChartIntegralModel.inclInf R F j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclInf R F j
  rw [← PrimeSpectrum.localization_away_comap_range ↥(TwoChartIntegralModel.chartAlgMid R F j)
    (TwoChartIntegralModel.jInvChartInf R F j), Spec.map_base]
  rfl

theorem ιInf_base_mem_range_ιFin_iff (xi : TwoChartIntegralModel.XInf R F j) :
    (TwoChartIntegralModel.ιInf R F j).base xi ∈ Set.range (TwoChartIntegralModel.ιFin R F j).base ↔
      TwoChartIntegralModel.jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf_base, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (TwoChartIntegralModel.fFin R F j) (TwoChartIntegralModel.fInf R F j) x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fFin R F j).base w,
      (pushout_inl_eq_inr_iff (TwoChartIntegralModel.fFin R F j) (TwoChartIntegralModel.fInf R F j) _ _).mpr ⟨w, rfl, rfl⟩⟩

end TwoChart

section Points

variable (p : ℕ) [Fact p.Prime]

scoped instance neZero_p : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

variable (k : Type) [Field k] [CharP k p]

def ψk (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →+* k := (algebraMap ℤ k).comp ψ.toRingHom

def ptMor (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) :
    Spec (CommRingCat.of k) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (ψk p k ψ)) ≫ (TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (𝟙 _) (by
    rw [Category.assoc, Category.id_comp,
      show DRModel.toBase p = TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) from rfl,
      TwoChartIntegralModel.ιInf_toBase, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext_int _ _)

def pt (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) :=
  (ptMor p k ψ).base (IsLocalRing.closedPoint k)

def chartPt (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) : TwoChartIntegralModel.XInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) :=
  (Spec.map (CommRingCat.ofHom (ψk p k ψ))).base (IsLocalRing.closedPoint k)

theorem fst_pt (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (pt p k ψ) =
      ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).base (chartPt p k ψ) := by
  show (ptMor p k ψ ≫ pullback.fst _ _).base (IsLocalRing.closedPoint k) = _
  rw [ptMor, pullback.lift_fst]
  rfl

theorem mem_chartPt_asIdeal_iff (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) (a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) : a ∈ (chartPt p k ψ).asIdeal ↔ (p : ℤ) ∣ ψ a := by
  rw [chartPt, Spec.map_base]
  change (ψk p k ψ) a ∈ (IsLocalRing.closedPoint k).asIdeal ↔ _
  change (algebraMap ℤ k) (ψ a) ∈ IsLocalRing.maximalIdeal k ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not, eq_intCast,
    CharP.intCast_eq_zero_iff k p]

theorem fst_pt_mem_range_ιFin_iff (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (pt p k ψ) ∈
        Set.range ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).base ↔ ¬ (p : ℤ) ∣ ψ (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
  rw [fst_pt, ιInf_base_mem_range_ιFin_iff, mem_chartPt_asIdeal_iff]

theorem pt_ne_of_exists (ψ ψ' : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) (a : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (h : ¬ (p : ℤ) ∣ ψ a) (h' : (p : ℤ) ∣ ψ' a) :
    pt p k ψ ≠ pt p k ψ' := by
  intro heq
  have h1 := congrArg (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base heq
  rw [fst_pt, fst_pt] at h1
  have h2 : chartPt p k ψ = chartPt p k ψ' := ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).isOpenEmbedding.injective h1
  have h3 : a ∈ (chartPt p k ψ').asIdeal := (mem_chartPt_asIdeal_iff p k ψ' a).mpr h'
  rw [← h2, mem_chartPt_asIdeal_iff] at h3
  exact h h3

theorem fst_pt_eq (ψ : ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) →ₐ[ℤ] ℤ) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (pt p k ψ) =
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).base
        (IsLocalRing.closedPoint k) := by
  rw [fst_pt, ← Category.assoc, ← Spec.map_comp]
  rfl

end Points

theorem order_jq' : (jq : LaurentSeries ℚ).order = -1 := by
  have hx0 : (jq : LaurentSeries ℚ) ≠ 0 := jq_ne_zero
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by rw [coeff_jq_neg_one]; exact one_ne_zero)
  · by_contra hlt
    push_neg at hlt
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (coeff_jq_of_lt hlt))

theorem coeff_zero_inv_jq : (jq⁻¹ : LaurentSeries ℚ).coeff 0 = 0 := by
  have hx0 : (jq : LaurentSeries ℚ) ≠ 0 := jq_ne_zero
  have hinv : (jq : LaurentSeries ℚ)⁻¹ ≠ 0 := inv_ne_zero hx0
  have h1 : jq.order + jq⁻¹.order = 0 := by
    rw [← HahnSeries.order_mul hx0 hinv, mul_inv_cancel₀ hx0, HahnSeries.order_one]
  apply HahnSeries.coeff_eq_zero_of_lt_order
  have := order_jq'
  omega

theorem main (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (k : Type) [Field k] [CharP k p] [IsAlgClosed k] :
    ∃ y₁ y₂ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), y₁ ≠ y₂ ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₁ ∉
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₂ ∉
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
  classical

  obtain ⟨jp, W₀, W₁, hjp, hp₀, hp₁, hneW, hgen, hcomplete, ht, hres₀, hres₁⟩ :=
    ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  obtain ⟨φ, hφ⟩ := ModularCurve.IgusaScheme.exists_algHom_int_chartAlgInf_eq_coeff_zero p
  obtain ⟨-, a₁, ha₁, hna₁⟩ := ModularCurve.DRModel.dvd_coeffZero_of_mem_nonunits_and_exists_not_dvd_of_prime p jp hjp W₀ W₁
    hp₀ hp₁ hneW hgen hcomplete ht φ hφ
  obtain ⟨w, θ, -, hww, hιw, -, -, -, ψ₀, hψ₀, hψ₀W₁, -⟩ :=
    ModularCurve.DRModel.exists_iso_and_algHom_chartAlgFin_comp_eq_and_involutive p hp jp hjp W₀ W₁
      hp₀ hp₁ hneW hgen hcomplete ht hres₀ hres₁ φ hφ

  have hφj : (p : ℤ) ∣ φ (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
    have h := hφ (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
    have hcoe : (((TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) :
        ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) :
        ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = jq⁻¹ := by
      rw [show ((TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) :
          ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) :
          ↥(modularFunctionFieldFull p)) = (IgusaScheme.jFull p)⁻¹ from rfl]
      push_cast
      rw [IgusaScheme.coe_jFull]
    rw [hcoe, coeff_zero_inv_jq] at h
    have h0 : φ (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) = 0 := by
      exact_mod_cast h
    rw [h0]
    exact dvd_zero _
  have hinf : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (pt p k φ) ∉
      Set.range (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base := by
    rw [fst_pt_mem_range_ιFin_iff, not_not]
    exact hφj

  have hw : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (pt p k ψ₀) =
      w.hom.base ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (pt p k φ)) := by
    rw [fst_pt_eq, fst_pt_eq]
    have := congrArg (fun f => (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) ≫ f).base (IsLocalRing.closedPoint k)) hψ₀
    simp only [Category.assoc] at this
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this ⊢
    exact this.symm
  have hwwx : ∀ x : ↥(DRModel p), w.hom.base (w.hom.base x) = x := fun x => by
    have := congrArg (fun f : DRModel p ⟶ DRModel p => f.base x) hww
    simpa using this
  refine ⟨pt p k φ, pt p k ψ₀, pt_ne_of_exists p k φ ψ₀ a₁ hna₁ (hψ₀W₁ a₁ ha₁), ?_, ?_⟩
  · rw [Scheme.Hom.image_top_eq_opensRange]
    exact hinf
  · rw [Scheme.Hom.image_top_eq_opensRange]
    change _ ∉ Set.range _
    rintro ⟨z, hz⟩
    apply hinf
    rw [← hwwx ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (pt p k φ)), ← hw, ← hz]
    refine ⟨(Spec.map (CommRingCat.ofHom θ.toRingHom)).base z, ?_⟩
    have := congrArg (fun f : TwoChartIntegralModel.XFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ⟶ DRModel p => f.base z) hιw
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
    exact this.symm

end ModularCurve.DRModel.Cusps2
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve.DRModel.Cusps2"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve.DRModel"
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve.DRModel P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre.ModularCurve.DRModel.Cusps2"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] :
    ∃ y₁ y₂ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), y₁ ≠ y₂ ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₁ ∉
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₂ ∉
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) :=
  ModularCurve.DRModel.Cusps2.main p hp k

end S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre
end P2MW
export P2MW.S_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre (solution)
