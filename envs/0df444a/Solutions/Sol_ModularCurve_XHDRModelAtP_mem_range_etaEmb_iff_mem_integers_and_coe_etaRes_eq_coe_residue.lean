-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2dbcf01e-6724-5c55-9267-feb75d5b0b58

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens
import Theorems.Thm_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 3200000 in
open Classical in
open ModularCurve in

/-!

                                                                                                                                     -/

namespace GENERICPT

open ModularCurve

set_option maxHeartbeats 3200000 in

theorem exists_mem_integers_and_coe_res_eq_coe_residue

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (Rg : AlgebraicCurve.RegularProlongation Pl ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)))
    (hRg₁ : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥Pl, ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x)
    (hRg₂ : ∀ (y : LaurentSeries ↥Pl) (hy : ModularCurve.coeffMap Pl.subtype y ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
        ∃ hO : (⟨ModularCurve.coeffMap Pl.subtype y, hy⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers,
          ((Rg.residue ⟨_, hO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)
    (hRg₃ : ∀ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hf : f ∈ Rg.integers) (x y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x →
        ((Rg.residue ⟨f, hf⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :
    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    letI res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
    ∀ g : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))),
      ∃ hO : (emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers,
        ((res g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          ((Rg.residue ⟨emb g, hO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
  intro g
  let emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
    𝔛.Meta.ffEquiv.symm.toRingHom.comp
      ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
        ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
  let res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
    (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom

  obtain ⟨U, hηU, s, hs⟩ := (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.exists_germ_eq g

  haveI : JacobsonSpace ↥(𝔛.Mfib Pl hPl ρ hρ).C :=
    LocallyOfFiniteType.jacobsonSpace (𝔛.Mfib Pl hPl ρ hρ).toBase
  have hgenV : genericPoint (𝔛.Mfib Pl hPl ρ hρ).C ∈ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U := hηU
  obtain ⟨P, hPV, hPcl⟩ := nonempty_inter_closedPoints (X := ↥(𝔛.Mfib Pl hPl ρ hρ).C)
    (Z := (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U : (𝔛.Mfib Pl hPl ρ hρ).C.Opens) : Set ↥(𝔛.Mfib Pl hPl ρ hρ).C)) ⟨_, hgenV⟩ ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U).2.isLocallyClosed
  have hzU : bc.base ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0).base P) ∈ U := by
    have : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base P ∈ U := hPV
    simpa only [Scheme.Hom.comp_apply] using this

  have hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U)) := ⟨⟨genericPoint 𝔛.Meta.C, hsp.mem_open U.2 hηU⟩⟩
  obtain ⟨hneM, xs, ys, hys, hgen, hred, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_gaussWitness_and_ffEquiv_symm_germToFunctionField_mfib_eq_of_mem_opens p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ ⟨P, hPcl⟩ U hzU hne s

  have E1 : emb g = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom s)) := by
    show 𝔛.Meta.ffEquiv.symm ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom g)) = _
    rw [← hs, TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

  haveI := hneM
  have E2 : res g = (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm ((𝔛.Mfib Pl hPl ρ hρ).C.germToFunctionField ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc) ⁻¹ᵁ U) (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).app U).hom s)) := by
    show (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm (((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom g) = _
    rw [← hs, Scheme.Hom.germ_stalkMap_apply]
  have hgen' : ((emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : LaurentSeries (AlgebraicClosure ℚ)) *
      ModularCurve.coeffMap Pl.subtype ys = ModularCurve.coeffMap Pl.subtype xs := by
    rw [E1]; exact hgen
  have hO : (emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨xs, ys, hys, hgen'⟩
  refine ⟨hO, ?_⟩
  have h3 := hRg₃ _ hO xs ys hys hgen'
  rw [E2]
  apply mul_right_cancel₀ hys
  rw [h3]
  exact hred

end GENERICPT

set_option maxHeartbeats 3200000 in
theorem solution

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)))

    (Rg : AlgebraicCurve.RegularProlongation Pl ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)))
    (hRg₁ : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥Pl, ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x)
    (hRg₂ : ∀ (y : LaurentSeries ↥Pl) (hy : ModularCurve.coeffMap Pl.subtype y ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
        ∃ hO : (⟨ModularCurve.coeffMap Pl.subtype y, hy⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers,
          ((Rg.residue ⟨_, hO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)
    (hRg₃ : ∀ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hf : f ∈ Rg.integers) (x y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x →
        ((Rg.residue ⟨f, hf⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    (hsp : gA.base (genericPoint 𝔛.Meta.C) ⤳ (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)) :

    letI emb : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.xHFunctionFieldBar M H) :=
      𝔛.Meta.ffEquiv.symm.toRingHom.comp
        ((gA.stalkMap (genericPoint 𝔛.Meta.C)).hom.comp
          ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalkSpecializes hsp).hom)
    letI res : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM)) :=
      (𝔛.Mfib Pl hPl ρ hρ).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)).hom
    (∀ f : ↥(ModularCurve.xHFunctionFieldBar M H), f ∈ emb.range ↔ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers) ∧
    (∀ (g : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.stalk ((𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ 0 ≫ bc).base (genericPoint (𝔛.Mfib Pl hPl ρ hρ).C)))) (hg : (emb g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers),
      ((res g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        ((Rg.residue ⟨emb g, hg⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) := by
  have GP := GENERICPT.exists_mem_integers_and_coe_res_eq_coe_residue p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂
    Rg hRg₁ hRg₂ hRg₃ hsp
  obtain ⟨hinj, ⟨V, hV, hVtop, hVmax⟩, -⟩ :=
    ModularCurve.XHDRModelAtP.injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
      p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρ hρ gA hgA₁ hgA₂ bc hbc₁ hbc₂ hsp
  refine ⟨fun f => ⟨?_, fun hf => ?_⟩, fun g hg => ?_⟩
  · rintro ⟨g, rfl⟩
    exact (GP g).1
  ·
    have hle : V ≤ (Rg.integers : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H)) := by
      intro x hx
      have hx' : x ∈ V.toSubring := hx
      rw [← hV] at hx'
      obtain ⟨g, rfl⟩ := hx'
      exact (GP g).1
    have hne : (Rg.integers : ValuationSubring ↥(ModularCurve.xHFunctionFieldBar M H)) ≠ ⊤ := by
      intro htop
      have hpinv : ((p : AlgebraicClosure ℚ))⁻¹ ∉ Pl := by
        intro h
        have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
        have h1 : Pl.valuation ((p : AlgebraicClosure ℚ))⁻¹ ≤ 1 := (Pl.valuation_le_one_iff _).mpr h
        have h2 : Pl.valuation (p : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff Pl).mp hPl
        rw [map_inv₀] at h1
        have hp0' : Pl.valuation (p : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr hp0
        exact absurd (h2.trans_le ((inv_le_one₀ (zero_lt_iff.mpr hp0')).mp h1)) (lt_irrefl _)
      apply hpinv
      have hmem : algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ((p : AlgebraicClosure ℚ))⁻¹ ∈ Rg.integers := by
        rw [htop]; exact ValuationSubring.mem_top _
      exact (Rg.algebraMap_mem_iff _).mp hmem
    rcases hVmax _ hle with h | h
    · have hfV : (f : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ V := by rw [← h]; exact hf
      have : f ∈ V.toSubring := hfV
      rwa [← hV] at this
    · exact absurd h hne
  · obtain ⟨hO, h⟩ := GP g
    exact h

#print axioms solution

end S_ModularCurve_XHDRModelAtP_mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue (solution)
