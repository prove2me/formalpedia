-- Prove2me | solution 1 for ModularCurve.reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bb46dcca-4cd3-5036-9711-9d64b91565ad

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
import Theorems.Thm_ModularCurve_exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
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

namespace P2MW.S_ModularCurve_reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_jqNGen ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

namespace D6aU

theorem mem_of_pow_mem {F : Type*} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ V) : x ∈ V := by
  rcases V.mem_or_inv_mem x with h | h
  · exact h
  · have key : x = x ^ n * (x⁻¹) ^ (n - 1) := by
      rcases eq_or_ne x 0 with rfl | hx0
      · simp [zero_pow hn.ne']
      · rw [inv_pow, ← pow_sub₀ _ hx0 (Nat.sub_le n 1), Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hn.ne'), pow_one]
    rw [key]
    exact V.toSubring.mul_mem hx (V.toSubring.pow_mem h _)

end D6aU

open D6aU ModularCurve in
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

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    [CharP K p]

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    :
    ∀ (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        ((f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap (frobenius K p) ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p * f' := by
  intro x y hyx
  classical
  haveI hMp : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩
  have hpMp : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h)

  obtain ⟨Rg, hRg₁, hRg₂, hRg₃⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (AlgebraicClosure ℚ) Pl (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)

  obtain ⟨D, f, yx, hDx, hf0, hdivf, hfy, hyx0, hΨx⟩ := hΨ x
  obtain ⟨D', f', yy, hDy, hf0', hdivf', hfy', hyy0, hΨy⟩ := hΨ y

  obtain ⟨hα, hβ, hPD, hfin, hN, D_U, hDU, hcls, hfU0, hdivU⟩ :=
    ModularCurve.exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
      p M hpM H S hin wgen D f hf0 hdivf
  have hDD' : (AlgebraicCurve.Pic0.mk D_U : ModularCurve.JH M H) = AlgebraicCurve.Pic0.mk D' := by
    rw [hcls, hDx, ← hyx, hDy]

  obtain ⟨h, c₀, hh0, hc0, -, hff'⟩ := ModularCurve.exists_eq_add_ord_and_eq_algebraMap_mul_mul_smul_pow_of_pic0Mk_eq
    p M H wgen D_U D' hDD' (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) f' hfU0 hf0' hdivU hdivf'

  have hfO : ((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yx, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy⟩
  have hf'O : ((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers :=
    (hRg₁ _).mpr ⟨yy, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]; exact hfy'⟩
  have hyx1 : ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yx := by
    have h1 := hRg₃ _ hfO yx 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy)
    rw [map_one, mul_one] at h1; exact h1
  have hyy1 : ((Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yy := by
    have h1 := hRg₃ _ hf'O yy 1 (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact hfy')
    rw [map_one, mul_one] at h1; exact h1

  obtain ⟨lamG, hlamG, hfUO, c, hc, hresU⟩ := ModularCurve.XHDRModelAtP.exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
    p hp2 M hpM hpM2 H hHp S hin Pl hPl K hj 𝔛 Λ hrepΛ O hD hDQ hsep ajQ kQ ajbar εbar hpoinc hajQε hajQ hkQ₁ hkQ₂ hajbar hajbar_over hεbar hεbar_aj hpts_law hAJ R hRA hRdvr hRirr hRfix hRmax 𝒢 Δ hΔinj hΔlev hΔgal hΔhecke wgen hwgen ιK hιK Ψ hΨ Rg hRg₁ hRg₂ hRg₃ d hd hdH θ hθ hwθ f hfO

  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq (c₀ / lamG) (Fact.out : p.Prime).pos
  set k : ↥(ModularCurve.xHFunctionFieldBar M H) := algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lam * (wgen • h) with hkdef
  have hk : f' = (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lamG * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H)))) * k ^ p := by
    have hl : algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lamG ≠ 0 := (map_ne_zero _).mpr hlamG
    rw [hff', hkdef, mul_pow, ← map_pow, hlam, map_div₀]
    field_simp

  have hres0 : Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ ≠ 0 := by
    intro h0; apply hyx0; rw [← hyx1, h0]; rfl
  have hres0' : Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ ≠ 0 := by
    intro h0; apply hyy0; rw [← hyy1, h0]; rfl
  have hσ0 : coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) ≠ 0 := by
    intro h0; apply hres0
    have hinj : Function.Injective (coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p)) := by
      intro a b hab; ext n
      exact frobenius_inj (IsLocalRing.ResidueField ↥Pl) p (by simpa [coeffMap_coeff] using congrArg (fun z => HahnSeries.coeff z n) hab)
    have h1 := hinj (h0.trans (map_zero _).symm)
    exact_mod_cast h1
  have hresU0 : Rg.residue ⟨_, hfUO⟩ ≠ 0 := by
    intro h0
    have := hresU
    rw [h0] at this
    simp only [ZeroMemClass.coe_zero] at this
    exact (mul_ne_zero (by simpa using hc) hσ0) this.symm
  have huU : IsUnit (⟨_, hfUO⟩ : ↥Rg.integers) := Rg.isUnit_of_residue_ne_zero hresU0
  have hu' : IsUnit (⟨_, hf'O⟩ : ↥Rg.integers) := Rg.isUnit_of_residue_ne_zero hres0'
  obtain ⟨uU, huUeq⟩ := huU
  obtain ⟨u', hu'eq⟩ := hu'
  have hfU0' : ((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lamG * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H)))) : ↥(ModularCurve.xHFunctionFieldBar M H)) ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hlamG) hfU0

  have hinvU : ((((uU⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) = ((((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lamG * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H)))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have : (((uU⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) * (((uU : (↥Rg.integers)ˣ) : ↥Rg.integers) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    rw [huUeq] at this
    exact this
  have hkpO : (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p ∈ Rg.integers := by
    have e1 : (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p = (((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) * ((((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lamG * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H)))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))⁻¹ := by
      have hne : ((((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lamG * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H)))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ≠ 0 := by exact_mod_cast hfU0'
      rw [eq_mul_inv_iff_mul_eq₀ hne]
      have := congrArg (fun z : ↥(ModularCurve.xHFunctionFieldBar M H) => ((z : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) hk
      beta_reduce at this
      simp only [this, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      exact mul_comm _ _
    rw [e1, ← hinvU]
    exact Rg.integers.toSubring.mul_mem hf'O ((uU⁻¹ : (↥Rg.integers)ˣ) : ↥Rg.integers).2
  have hkO : ((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers := D6aU.mem_of_pow_mem Rg.integers (Fact.out : p.Prime).pos hkpO

  have hprod : (⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥Rg.integers) = ⟨_, hfUO⟩ * ⟨_, hkO⟩ ^ p := by
    apply Subtype.ext
    show (((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) = ((((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lamG * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p); wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H)))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) * (((k : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) ^ p
    have := congrArg (fun z : ↥(ModularCurve.xHFunctionFieldBar M H) => ((z : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) hk
    beta_reduce at this
    simp only [this, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hresf' : ((Rg.residue ⟨((f' : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf'O⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
      HahnSeries.C c * coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) *
        ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) ^ p := by
    rw [hprod, map_mul, map_pow]
    push_cast
    rw [hresU]

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal ↥Pl, ιK a = 0 := fun a ha =>
    (hιK a).mpr ((ValuationSubring.valuation_lt_one_iff Pl a).mp ha)
  let j : (IsLocalRing.ResidueField ↥Pl) →+* K := Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥Pl) ιK hker
  have hjι : j.comp (IsLocalRing.residue ↥Pl) = ιK := RingHom.ext fun a => rfl
  have hcoe : ∀ z : LaurentSeries ↥Pl, coeffMap ιK z = coeffMap j (coeffMap (IsLocalRing.residue ↥Pl) z) := fun z => by
    rw [coeffMap_coeffMap, hjι]
  have hjfrob : ∀ z : LaurentSeries (IsLocalRing.ResidueField ↥Pl), coeffMap j (coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) z) = coeffMap (frobenius K p) (coeffMap j z) := by
    intro z
    rw [coeffMap_coeffMap, coeffMap_coeffMap]
    congr 1
    ext a
    simp [frobenius_def, map_pow]
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hΨx' : ((Ψ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = coeffMap j ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
    rw [hΨx, hcoe, hyx1]

  have hle := ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup p M hpM hpM2 H hHp (IsLocalRing.ResidueField ↥Pl)
  have hσmem : coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) ∈
      ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) := by
    have e2 : coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) ((Rg.residue ⟨((f : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hfO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
        HahnSeries.C c⁻¹ * ((Rg.residue ⟨_, hfUO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by
      rw [hresU, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [e2]
    apply hle
    refine mul_mem ?_ (Rg.residue ⟨_, hfUO⟩).2
    have h4 := (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)).algebraMap_mem c⁻¹
    rwa [ModularCurve.algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply] at h4
  have hkmem : ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) ∈ ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) :=
    hle (Rg.residue ⟨_, hkO⟩).2

  refine ⟨j c, ⟨coeffMap j ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)), ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j _ hkmem⟩,
    ⟨coeffMap (frobenius K p) ((Ψ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K), ?_⟩, (map_ne_zero j).mpr hc, rfl, ?_⟩
  · rw [hΨx', ← hjfrob]
    exact ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem j _ hσmem
  · have final : ((Ψ y : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) =
        HahnSeries.C (j c) * (coeffMap j ((Rg.residue ⟨_, hkO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ^ p *
          coeffMap (frobenius K p) ((Ψ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) := by
      rw [hΨy, hcoe, ← hyy1, hresf', map_mul, map_mul, map_pow, hjfrob, ← hΨx', HahnSeries.C_apply, coeffMap_single,
        ← HahnSeries.C_apply]
      ring
    apply Subtype.ext
    rw [final]
    push_cast
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]

#print axioms solution

end S_ModularCurve_reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv
end P2MW
export P2MW.S_ModularCurve_reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv (solution)
