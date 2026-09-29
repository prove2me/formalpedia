-- Prove2me | solution 1 for ModularCurve.ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ef97d3b7-8e17-55b9-a424-4e6382d5ead4

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet
import Theorems.Thm_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective"
open scoped MatrixGroups

namespace HUgen

section HasValue
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem hasValue_sub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') : v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hga⟩ := h
  obtain ⟨hg', hga'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [this, map_sub, hga, hga', ← map_sub]

theorem hasValue_pow {g : F} {a : K} (h : v.HasValue g a) : ∀ n : ℕ, v.HasValue (g ^ n) (a ^ n)
  | 0 => by rw [pow_zero, pow_zero]; exact Place.hasValue_one v
  | n + 1 => by rw [pow_succ, pow_succ]; exact (hasValue_pow h n).mul h

theorem hasValue_prod {ι : Type*} (s : Finset ι) (g : ι → F) (a : ι → K) (h : ∀ i ∈ s, v.HasValue (g i) (a i)) :
    v.HasValue (∏ i ∈ s, g i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact Place.hasValue_one v
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end HasValue

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {τ : R →+* S} (hτ : Function.Injective τ) :
    Function.Injective (coeffMap τ) := by
  intro a b h; ext n; exact hτ (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

universe u

theorem core (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (κ : Type u) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (Γ : Subgroup SL(2, ℤ)) (S : Finset κ) (hS : ∀ a, a ∈ S ↔ a ∈ ssJSet p κ)
    (x : LaurentSeries ℤ) (hx : coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (g : ↥(qExpFunctionFieldC κ Γ)) (hg : ((g : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = coeffMap (Int.castRingHom κ) x)
    (v : Place κ ↥(qExpFunctionFieldC κ Γ))
    (xj : ↥(qExpFunctionFieldC κ Γ)) (hxj : ((xj : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = jqModC κ)
    (a : κ) (hva : v.HasValue (xj : ↥(qExpFunctionFieldC κ Γ)) a) (haS : a ∉ S) :
    v.ord (g : ↥(qExpFunctionFieldC κ Γ)) = 0 := by
  classical
  obtain ⟨x', hx', hprod⟩ := ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet p hp
  have hxx : x = x' := coeffMap_injective (τ := Int.castRingHom ℚ) (Int.cast_injective) (hx.trans hx'.symm)
  have hκ : coeffMap (Int.castRingHom κ) x = ∏ a ∈ S, (jqModC κ - HahnSeries.C a) ^ (12 / jWidth a) := by
    rw [hxx]; exact hprod κ S hS
  have hgF : g = ∏ a' ∈ S, (xj - algebraMap κ ↥(qExpFunctionFieldC κ Γ) a') ^ (12 / jWidth a') := by
    apply Subtype.ext
    rw [hg, hκ, SubmonoidClass.coe_finset_prod]
    refine Finset.prod_congr rfl fun a' _ => ?_
    rw [SubmonoidClass.coe_pow]
    congr 1
    rw [AddSubgroupClass.coe_sub, hxj]
    congr 1
    rw [HahnSeries.C_apply, ← ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl
  have hfac : ∀ a' ∈ S, v.HasValue (xj - algebraMap κ ↥(qExpFunctionFieldC κ Γ) a') (a - a') := fun a' _ =>
    hasValue_sub v hva (Place.hasValue_algebraMap v a')
  have h := hasValue_prod v S (fun a' => (xj - algebraMap κ ↥(qExpFunctionFieldC κ Γ) a') ^ (12 / jWidth a')) (fun a' => (a - a') ^ (12 / jWidth a'))
    (fun a' ha' => hasValue_pow v (hfac a' ha') _)
  rw [← hgF] at h
  refine h.ord_eq_zero ?_
  rw [Finset.prod_ne_zero_iff]
  intro a' ha'
  apply pow_ne_zero
  intro h0
  exact haS ((sub_eq_zero.mp h0) ▸ ha')

theorem all (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (hfin : (ssJSet p κ).Finite)
    (Γ : Subgroup SL(2, ℤ))
    (x : LaurentSeries ℤ) (hx : coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (g : ↥(qExpFunctionFieldC κ Γ)) (hg : ((g : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = coeffMap (Int.castRingHom κ) x)
    (v : Place κ ↥(qExpFunctionFieldC κ Γ))
    (xj : ↥(qExpFunctionFieldC κ Γ)) (hxj : ((xj : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = jqModC κ)
    (a : κ) (hva : v.HasValue (xj : ↥(qExpFunctionFieldC κ Γ)) a) (ha : a ∉ ssJSet p κ) :
    v.ord (g : ↥(qExpFunctionFieldC κ Γ)) = 0 := by
  classical
  by_cases hp : 5 ≤ p
  · exact core p hp κ Γ hfin.toFinset (fun a => by rw [Set.Finite.mem_toFinset]) x hx g hg v xj hxj a hva
      (by rw [Set.Finite.mem_toFinset]; exact ha)
  · have hp' : p < 5 := not_le.mp hp
    obtain ⟨x', hx', hpow⟩ := ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five p hp'
    have hxx : x = x' := coeffMap_injective (τ := Int.castRingHom ℚ) (Int.cast_injective) (hx.trans hx'.symm)
    have hgF : g = xj ^ (p - 1) := by
      apply Subtype.ext
      rw [hg, hxx, hpow κ, SubmonoidClass.coe_pow, hxj]
    have h := hasValue_pow v hva (p - 1)
    rw [← hgF] at h
    refine h.ord_eq_zero (pow_ne_zero _ ?_)
    intro ha0
    apply ha
    rw [ha0]
    exact ModularCurve.zero_mem_ssJSet_of_lt_five hp'

end HUgen

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p] [IsAlgClosed κ] (Γ : Subgroup SL(2, ℤ))
    (x : LaurentSeries ℤ)
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p)
    (g : ↥(qExpFunctionFieldC κ Γ)) (hg : ((g : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = coeffMap (Int.castRingHom κ) x)
    (v : Place κ ↥(qExpFunctionFieldC κ Γ)) (hv : v ∉ ssPlacesQExp κ Γ p)

    (xj : ↥(qExpFunctionFieldC κ Γ)) (hxj : ((xj : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ) = jqModC κ)
    (a : κ) (hva : v.HasValue (xj : ↥(qExpFunctionFieldC κ Γ)) a) :
    v.ord (g : ↥(qExpFunctionFieldC κ Γ)) = 0 := by
  classical
  have ha : a ∉ @ssJSet p κ _ (Classical.decEq κ) := by
    intro h
    exact hv ⟨xj, a, hxj, hva, h⟩
  have ha' : a ∉ ssJSet p κ := by convert ha
  exact HUgen.all p κ (ModularCurve.ssJSet_finite p κ) Γ x hx g hg v xj hxj a hva ha'

end S_ModularCurve_ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries (solution)
