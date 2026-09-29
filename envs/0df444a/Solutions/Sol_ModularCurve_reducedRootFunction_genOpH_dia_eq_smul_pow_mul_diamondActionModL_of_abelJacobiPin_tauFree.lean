-- Prove2me | solution 1 for ModularCurve.reducedRootFunction_genOpH_dia_eq_smul_pow_mul_diamondActionModL_of_abelJacobiPin_tauFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4b1d26d7-1ddc-5a2b-9be6-11b9e87e075a

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
import Theorems.Thm_ModularCurve_XHDRModelAtP_injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL
import Theorems.Thm_ModularCurve_coeffMap_coe_apply_eq_coe_apply_coeffMap_of_isDiamondPullbackModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reducedRootFunction_genOpH_dia_eq_smul_pow_mul_diamondActionModL_of_abelJacobiPin_tauFree
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

namespace D6aFrame

open ModularCurve

theorem exists_ringHom_ratLocalizedAt (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p) :
    ∃ ρ : R p →+* ↥Pl, Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ) := by
  have hmem : ∀ q : R p, algebraMap (R p) (AlgebraicClosure ℚ) q ∈ Pl.toSubring := by
    intro q
    have hq : ((q : ℚ).den).Coprime p := q.2
    have hnd : ¬ (p : ℤ) ∣ ((q : ℚ).den : ℤ) := by
      intro h
      have h' : p ∣ (q : ℚ).den := by exact_mod_cast h
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hq.symm h')
    obtain ⟨u, hu⟩ := ValuationSubring.intCast_isUnit_of_not_dvd (Fact.out : p.Prime) hPl hnd
    have hcast : algebraMap (R p) (AlgebraicClosure ℚ) q =
        (((q : ℚ).num : ℤ) : AlgebraicClosure ℚ) * ((((q : ℚ).den : ℤ) : AlgebraicClosure ℚ))⁻¹ := by
      rw [IsScalarTower.algebraMap_apply (R p) ℚ (AlgebraicClosure ℚ), eq_ratCast]
      show (((q : ℚ)) : AlgebraicClosure ℚ) = _
      rw [Rat.cast_def, div_eq_mul_inv]
      push_cast
      rfl
    have hu' : ((((q : ℚ).den : ℤ) : AlgebraicClosure ℚ)) = ((u : ↥Pl) : AlgebraicClosure ℚ) := by
      rw [hu]; push_cast; rfl
    have hinv : ((((q : ℚ).den : ℤ) : AlgebraicClosure ℚ))⁻¹ = ((↑u⁻¹ : ↥Pl) : AlgebraicClosure ℚ) := by
      rw [hu']
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    rw [hcast, hinv]
    exact Pl.toSubring.mul_mem (intCast_mem _ _) (↑u⁻¹ : ↥Pl).2
  exact ⟨(algebraMap (R p) (AlgebraicClosure ℚ)).codRestrict Pl.toSubring hmem, rfl⟩

section
variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
  (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

noncomputable def gA (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    𝔛.Meta.C ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) :=
  pullback.lift (𝔛.eeta ≫ pullback.fst _ _) (𝔛.Meta.toBase ≫ barPt Pl) (by
    have h1 : barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) = Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
      rw [barPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
    rw [Category.assoc, Category.assoc, pullback.condition, h1, ← Category.assoc, 𝔛.heeta])

theorem gA_fst (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    gA p M hpM H hj 𝔛 Pl ρ hρ ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

theorem gA_snd (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    gA p M hpM H hj 𝔛 Pl ρ hρ ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl := pullback.lift_snd _ _ _

noncomputable def bc (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥Pl) :
    fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ) ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

theorem bc_fst (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥Pl) :
    bc p M H hj Pl ρ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
theorem bc_snd (Pl : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥Pl) :
    bc p M H hj Pl ρ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) :=
  pullback.lift_snd _ _ _

theorem hsp (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj) (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (z : ↥(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) :
    (gA p M hpM H hj 𝔛 Pl ρ hρ).base (genericPoint 𝔛.Meta.C) ⤳ z := by
  have h1 : barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ) = Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [barPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]

  haveI := 𝔛.flat
  have hgen : GeneralizingMap (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
    Flat.generalizingMap _
  have hbot : (⊥ : PrimeSpectrum ↥Pl) ⤳ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base z :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨ζ, hζz, hζ⟩ := hgen hbot

  have hpt : (barPt Pl).base (⊥ : PrimeSpectrum (AlgebraicClosure ℚ)) = (⊥ : PrimeSpectrum ↥Pl) := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective _ Subtype.val_injective
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (g := barPt Pl) ζ (⊥ : PrimeSpectrum (AlgebraicClosure ℚ)) (hζ.trans hpt.symm)

  let ψ := pullbackLeftPullbackSndIso (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) (barPt Pl)
  let cg : pullback (toBase p (ΓM M H) hj) (barPt Pl ≫ Spec.map (CommRingCat.ofHom ρ)) ≅
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) :=
    pullback.congrHom rfl h1
  have hident : pullback.fst (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) (barPt Pl) =
      ψ.hom ≫ cg.hom ≫ inv 𝔛.eeta ≫ gA p M hpM H hj 𝔛 Pl ρ hρ := by
    have hinv : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
      rw [IsIso.inv_comp_eq, 𝔛.heeta]
    apply pullback.hom_ext
    · simp only [Category.assoc, gA_fst, IsIso.inv_hom_id_assoc]
      dsimp only [cg, ψ, pullback.congrHom, pullback.map]
      rw [asIso_hom, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    · rw [pullback.condition]
      simp only [Category.assoc, gA_snd]
      rw [reassoc_of% hinv]
      dsimp only [cg, ψ, pullback.congrHom, pullback.map]
      rw [asIso_hom, pullback.lift_snd_assoc, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc]
  set m := (inv 𝔛.eeta).base (cg.hom.base (ψ.hom.base w)) with hm
  have hmζ : (gA p M hpM H hj 𝔛 Pl ρ hρ).base m = ζ := by
    rw [← hw, hident]; rfl
  have hξm : genericPoint 𝔛.Meta.C ⤳ m := (genericPoint_spec 𝔛.Meta.C).specializes (by trivial)
  rw [← hmζ] at hζz
  exact (hξm.map (gA p M hpM H hj 𝔛 Pl ρ hρ).base.hom.continuous).trans hζz

end

theorem mem_of_pow_mem {F : Type*} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ V) : x ∈ V := by
  rcases V.mem_or_inv_mem x with h | h
  · exact h
  · have key : x = x ^ n * (x⁻¹) ^ (n - 1) := by
      rcases eq_or_ne x 0 with rfl | hx0
      · simp [zero_pow hn.ne']
      · rw [inv_pow, ← pow_sub₀ _ hx0 (Nat.sub_le n 1), Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hn.ne'), pow_one]
    rw [key]
    exact V.toSubring.mul_mem hx (V.toSubring.pow_mem h _)

end D6aFrame

open D6aFrame ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)
    :
    ∀ (e : (ZMod M)ˣ) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.dia e) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p *
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM)
              (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (Ψ x)) := by
  intro e x y hyx
  classical
  haveI hMp : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩

  obtain ⟨ρPl, hρPl⟩ := D6aFrame.exists_ringHom_ratLocalizedAt p Pl hPl
  have hspec := D6aFrame.hsp p M hpM H hj 𝔛 Pl ρPl hρPl
    ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).base (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C))
  obtain ⟨Rg, hRg₁, hRg₂, hRg₃⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (AlgebraicClosure ℚ) Pl (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)

  obtain ⟨hinj, ⟨V, hV, -, -⟩, -⟩ := ModularCurve.XHDRModelAtP.injective_etaEmb_and_exists_valuationSubring_range_eq_rankOne_and_const
    p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρPl hρPl _ (gA_fst p M hpM H hj 𝔛 Pl ρPl hρPl) (gA_snd p M hpM H hj 𝔛 Pl ρPl hρPl)
    _ (bc_fst p M H hj Pl ρPl) (bc_snd p M H hj Pl ρPl) hspec
  obtain ⟨hmem, hres⟩ := ModularCurve.XHDRModelAtP.mem_range_etaEmb_iff_mem_integers_and_coe_etaRes_eq_coe_residue
    p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρPl hρPl _ (gA_fst p M hpM H hj 𝔛 Pl ρPl hρPl) (gA_snd p M hpM H hj 𝔛 Pl ρPl hρPl)
    _ (bc_fst p M H hj Pl ρPl) (bc_snd p M H hj Pl ρPl) Rg hRg₁ hRg₂ hRg₃ hspec
  have hpMp : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)
  have hκN : ((M / p : ℕ) : (IsLocalRing.ResidueField ↥Pl)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥Pl) p]; exact hpMp
  have hDPκ := ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed (IsLocalRing.ResidueField ↥Pl) (M / p) hκN (ModularCurve.infSubgroup p M H hpM)
  have hDIA := ModularCurve.XHDRModelAtP.exists_etaEmb_eq_diamondAutHBar_and_etaRes_eq_diamondActionModL
    p M hpM hpM2 H hHp Pl hPl hj 𝔛 ρPl hρPl _ (gA_fst p M hpM H hj 𝔛 Pl ρPl hρPl) (gA_snd p M hpM H hj 𝔛 Pl ρPl hρPl)
    _ (bc_fst p M H hj Pl ρPl) (bc_snd p M H hj Pl ρPl) hspec hDPκ

  obtain ⟨D, f, yx, hDx, hf0, hdivf, hfy, hyx0, hΨx⟩ := hΨ x
  obtain ⟨D', f', yy, hDy, hf0', hdivf', hfy', hyy0, hΨy⟩ := hΨ y
  obtain ⟨hcls, hdivσ⟩ := ModularCurve.XHDRModelAtP.mk_degZeroSMulHom_diamondAutHBar_eq_genOpH_dia_and_forall_mul_smul_eq_ord
    p M hpM H S hj 𝔛 wgen hwgen e D f hdivf
  have hDD' : (AlgebraicCurve.Pic0.mk (SemilinearAut.degZeroSMulHom (SemilinearAut.ofAlgAut (diamondAutHBar M H e)) D) : ModularCurve.JH M H) =
      AlgebraicCurve.Pic0.mk D' := by
    rw [hcls, hDx, ← hyx, hDy]
  have hσf0 : diamondAutHBar M H e f ≠ 0 := (map_ne_zero_iff _ (diamondAutHBar M H e).injective).mpr hf0
  obtain ⟨h, c₀, hh0, hc0, -, hff'⟩ := ModularCurve.exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
    p M H wgen _ D' hDD' (diamondAutHBar M H e f) f' hσf0 hf0' hdivσ hdivf'

  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq c₀ (Fact.out : p.Prime).pos
  set k : ↥(ModularCurve.xHFunctionFieldBar M H) := algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lam * (wgen • h) with hkdef
  have hk : f' = diamondAutHBar M H e f * k ^ p := by
    rw [hff', hkdef, mul_pow, ← map_pow, hlam]; ring

  have hfO : ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yx, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy⟩
  have hf'O : ((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yy, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy'⟩
  obtain ⟨g, hg⟩ := (hmem f).mpr hfO
  obtain ⟨g', hg'⟩ := (hmem f').mpr hf'O
  obtain ⟨ge, hge, hgeres⟩ := hDIA e g

  have hgO : (((𝔛.Meta.ffEquiv.symm.toRingHom.comp (((D6aFrame.gA p M hpM H hj 𝔛 Pl ρPl hρPl).stalkMap (genericPoint 𝔛.Meta.C)).hom.comp ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρPl))).presheaf.stalkSpecializes hspec).hom)) g : ↥(ModularCurve.xHFunctionFieldBar M H)) :
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers := by
    rw [hg]; exact hfO
  have hg'O : (((𝔛.Meta.ffEquiv.symm.toRingHom.comp (((D6aFrame.gA p M hpM H hj 𝔛 Pl ρPl hρPl).stalkMap (genericPoint 𝔛.Meta.C)).hom.comp ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρPl))).presheaf.stalkSpecializes hspec).hom)) g' : ↥(ModularCurve.xHFunctionFieldBar M H)) :
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers := by
    rw [hg']; exact hf'O
  have hresg := hres g hgO
  have hresg' := hres g' hg'O
  have hyx1 : ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yx := by
    have h1 := hRg₃ _ hfO yx 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy)
    rw [map_one, mul_one] at h1; exact h1
  have hyy1 : ((Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yy := by
    have h1 := hRg₃ _ hf'O yy 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy')
    rw [map_one, mul_one] at h1; exact h1
  have hresg1 : ((((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yx := by
    rw [hresg, ← hyx1]; congr 2; exact Subtype.ext hg
  have hresg'1 : ((((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g' : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yy := by
    rw [hresg', ← hyy1]; congr 2; exact Subtype.ext hg'

  have hunit : ∀ gg : ↥((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρPl))).presheaf.stalk ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).base (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C))), ((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) gg ≠ 0 → IsUnit gg := by
    intro gg hgg
    have h1 : IsUnit (((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom gg) := by
      apply isUnit_iff_ne_zero.mpr
      intro h0; apply hgg
      show (𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm (((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom gg) = 0
      rw [h0, map_zero]
    exact (isUnit_map_iff ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom gg).mp h1
  have hresg0 : ((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g ≠ 0 := by
    intro h0; apply hyx0; rw [← hresg1, h0]; rfl
  have hresg'0 : ((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g' ≠ 0 := by
    intro h0; apply hyy0; rw [← hresg'1, h0]; rfl
  have hresge0 : ((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) ge ≠ 0 := by
    rw [hgeres]; exact (map_ne_zero_iff _ (AlgEquiv.injective _)).mpr hresg0
  obtain ⟨ue, rfl⟩ := hunit ge hresge0

  have hkp : k ^ p = (𝔛.Meta.ffEquiv.symm.toRingHom.comp (((D6aFrame.gA p M hpM H hj 𝔛 Pl ρPl hρPl).stalkMap (genericPoint 𝔛.Meta.C)).hom.comp ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρPl))).presheaf.stalkSpecializes hspec).hom)) (g' * ↑ue⁻¹) := by
    rw [map_mul, map_units_inv, hg', hge, hg, hk, mul_comm, inv_mul_cancel_left₀ hσf0]
  have hkV : k ∈ V := by
    apply D6aFrame.mem_of_pow_mem V (Fact.out : p.Prime).pos
    show k ^ p ∈ V.toSubring
    rw [← hV, hkp]
    exact ⟨_, rfl⟩
  obtain ⟨gk, hgk⟩ : k ∈ ((𝔛.Meta.ffEquiv.symm.toRingHom.comp (((D6aFrame.gA p M hpM H hj 𝔛 Pl ρPl hρPl).stalkMap (genericPoint 𝔛.Meta.C)).hom.comp ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρPl))).presheaf.stalkSpecializes hspec).hom))).range := by rw [hV]; exact hkV
  have hg'eq : g' = ↑ue * gk ^ p := hinj (by rw [map_mul, map_pow, hgk, hge, hg, hg', hk])
  have hRES : ((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g' =
      diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g) *
        (((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) gk) ^ p := by
    rw [hg'eq, map_mul, map_pow, hgeres]

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal ↥Pl, ιK a = 0 := fun a ha =>
    (hιK a).mpr ((ValuationSubring.valuation_lt_one_iff Pl a).mp ha)
  let j : (IsLocalRing.ResidueField ↥Pl) →+* K := Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥Pl) ιK hker
  have hjι : j.comp (IsLocalRing.residue ↥Pl) = ιK := RingHom.ext fun a => rfl
  have hcoe : ∀ z : LaurentSeries ↥Pl, coeffMap ιK z = coeffMap j (coeffMap (IsLocalRing.residue ↥Pl) z) := fun z => by
    rw [coeffMap_coeffMap, hjι]
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hKN : ((M / p : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]; exact hpMp
  have hDPK := ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed K (M / p) hKN (ModularCurve.infSubgroup p M H hpM)
  have hρκ := ModularCurve.isDiamondPullbackModL_diamondActionModL hDPκ
  have hρK := ModularCurve.isDiamondPullbackModL_diamondActionModL hDPK
  have hΨx' : ((Ψ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = coeffMap j ((((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
    rw [hΨx, hcoe, hresg1]
  have hΨy' : ((Ψ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = coeffMap j ((((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g' : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
    rw [hΨy, hcoe, hresg'1]
  have key0 := ModularCurve.coeffMap_coe_apply_eq_coe_apply_coeffMap_of_isDiamondPullbackModL (IsLocalRing.ResidueField ↥Pl) K j (M / p) hκN (ModularCurve.infSubgroup p M H hpM)
    _ _ hρκ hρK (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g)
  have hΨxe : (⟨coeffMap j ((((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)),
      ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) (((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g).2⟩ :
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) = Ψ x := Subtype.ext hΨx'.symm
  rw [hΨxe] at key0
  have key : ((diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (Ψ x) :
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
      coeffMap j ((diamondActionModL (IsLocalRing.ResidueField ↥Pl) (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) g) :
        ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := key0.symm

  refine ⟨1, ⟨coeffMap j ((((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) gk : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)),
      ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) (((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) gk).2⟩, one_ne_zero, ?_⟩
  apply Subtype.ext
  have hfin : ((Ψ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
      (coeffMap j ((((𝔛.Mfib Pl hPl ρPl hρPl).ffEquiv.symm.toRingHom.comp ((𝔛.efib Pl hPl ρPl hρPl ≫ 𝔛.comp Pl hPl ρPl hρPl 0 ≫ D6aFrame.bc p M H hj Pl ρPl).stalkMap (genericPoint (𝔛.Mfib Pl hPl ρPl hρPl).C)).hom) gk : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ^ p *
        ((diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)) (Ψ x) : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) := by
    rw [hΨy', hRES, MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ← key, mul_comm]
  rw [map_one, one_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  exact hfin

#print axioms solution

end S_ModularCurve_reducedRootFunction_genOpH_dia_eq_smul_pow_mul_diamondActionModL_of_abelJacobiPin_tauFree
end P2MW
export P2MW.S_ModularCurve_reducedRootFunction_genOpH_dia_eq_smul_pow_mul_diamondActionModL_of_abelJacobiPin_tauFree (solution)
