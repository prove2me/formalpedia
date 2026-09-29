-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fd43e8f5-5503-5dcb-ae0b-5233109bac87

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_XHDRModelAtP_atkinLehner_swap_and_exists_coe_eq_modularUnitSeries_and_isInftySide_smul_iff_isZeroSide_of_wgen
import Theorems.Thm_ModularCurve_algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm
import Theorems.Thm_ModularCurve_exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jqNGen ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace VUnitAsm

theorem ord_algEquiv_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (P : Place K F) (g : F) :
    (σ • P).ord g = P.ord (σ.symm g) := by
  conv_lhs => rw [← σ.apply_symm_apply g]
  exact Place.ord_smul σ P _

theorem smul_symm_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (P : Place K F) :
    σ • σ.symm • P = P := by
  rw [smul_smul, show σ * σ.symm = 1 from AlgEquiv.ext fun a => by simp [AlgEquiv.mul_apply], one_smul]

theorem symm_apply_eq_of_apply_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (θ : F ≃ₐ[K] F) (G : F) (c : K)
    (hc : c ≠ 0) (hG : G ≠ 0) (h : θ G = algebraMap K F c * G⁻¹) : θ.symm G = algebraMap K F c * G⁻¹ := by
  have h1 : G = algebraMap K F c * (θ.symm G)⁻¹ := by
    have := congrArg θ.symm h
    rwa [θ.symm_apply_apply, map_mul, map_inv₀, AlgEquiv.commutes] at this
  have hs : θ.symm G ≠ 0 := (map_ne_zero_iff θ.symm θ.symm.injective).mpr hG
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).mpr hc
  have h2 : G * θ.symm G = algebraMap K F c := by
    calc G * θ.symm G = (algebraMap K F c * (θ.symm G)⁻¹) * θ.symm G := by rw [← h1]
      _ = algebraMap K F c := by rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]
  rw [eq_mul_inv_iff_mul_eq₀ hG, mul_comm]
  exact h2

end VUnitAsm

open VUnitAsm in
set_option maxHeartbeats 6400000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    :
    ∃ (G : ↥(xHFunctionFieldBar M H)) (m : ℕ) (c : AlgebraicClosure ℚ) (S₀ : Finset (ResidueField ↥A)) (n : ResidueField ↥A → ℕ) (e : ResidueField ↥A)
      (hG₁ : G ∈ Rpd.R₁.integers),

      (c ≠ 0 ∧ A.valuation c < 1) ∧

      (e ≠ 0 ∧ (∀ a ∈ S₀, a ∈ @ssJSet p (ResidueField ↥A) _ (Classical.decEq _)) ∧ (∑ a ∈ S₀, n a = m) ∧
        ∀ xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
          Rpd.R₁.residue ⟨G, hG₁⟩ =
            algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) e * ∏ a ∈ S₀, (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) a) ^ n a) ∧

      θ G = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c * G⁻¹ ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ¬ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V → V.ord G = 0) ∧

      (∀ x : ↥(xHFunctionFieldBar M H), ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
        ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C → C.ord G = (m : ℤ) * C.ord x) ∧
      (∀ x' : ↥(xHFunctionFieldBar M H), ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) →
        ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C → C.ord G = -((m : ℤ) * C.ord x')) := by
  have hp : p.Prime := Fact.out

  obtain ⟨hswap, ⟨G, hG⟩, hX⟩ :=
    ModularCurve.XHDRModelAtP.atkinLehner_swap_and_exists_coe_eq_modularUnitSeries_and_isInftySide_smul_iff_isZeroSide_of_wgen
      p M H hpM hpM2 hj 𝔛 A θ α hwgen hα_coe hβ_coe

  have hθexp : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f u hfu
    have hf : f = α u := Subtype.ext (by rw [hα_coe]; exact hfu)
    rw [hf]
    exact hβ_coe u
  have hT : ∀ G : ↥(xHFunctionFieldBar M H),
      ((G : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) →
        θ G = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((p : AlgebraicClosure ℚ) ^ 12) * G⁻¹ :=
    fun G hG => ModularCurve.algEquiv_apply_eq_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_of_qExpand_of_arithmeticGalois_comm
      p M H hpM hpM2 hHp hj θ hθexp hθgal G hG

  obtain ⟨S₀, n, hG₁, -, hS₀, -, hsum, -, hres⟩ :=
    ModularCurve.exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries p A (xHFunctionFieldBar M H)
      (qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM)) Rpd.R₁ Rpd.residue₁_coeffMap G hG
  have hG0 : G ≠ 0 := by
    intro h
    have h' := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
    simp only [hG, ZeroMemClass.coe_zero, map_eq_zero_iff _ (coeffEmb (AlgebraicClosure ℚ)).injective] at h'
    exact modularUnitSeries_ne_zero p h'
  have hc0 : ((p : AlgebraicClosure ℚ) ^ 12) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hcv : A.valuation ((p : AlgebraicClosure ℚ) ^ 12) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' ((ValuationSubring.mem_nonunits_iff A).mp hA) (by norm_num)
  have hm : (((p - 1 : ℕ) : ℤ)) = (p : ℤ) - 1 := by rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hres' : ∀ xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A),
      ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
        Rpd.R₁.residue ⟨G, hG₁⟩ =
          algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) 1 *
            ∏ a ∈ S₀, (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) a) ^ n a := by
    intro xb hxb
    rw [map_one, one_mul]
    exact hres xb hxb
  have hss : ∀ a ∈ S₀, a ∈ @ssJSet p (ResidueField ↥A) _ (Classical.decEq _) := fun a ha => (hS₀ a).mp ha
  refine ⟨G, p - 1, (p : AlgebraicClosure ℚ) ^ 12, S₀, n, 1, hG₁, ⟨hc0, hcv⟩, ⟨one_ne_zero, hss, hsum, hres'⟩, hT G hG, ?_, ?_, ?_⟩
  ·
    intro V hV
    by_contra h
    exact hV (ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries p M H hpM A G hG V h)
  ·
    intro x hx C hC
    rw [hm]
    exact ModularCurve.JHPlaceSpecialization.ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide p M H hpM A G hG x hx C hC
  ·
    intro x' hx' C hC
    have hC' := hC
    obtain ⟨-, x, -, hx, -, -⟩ := hC'
    obtain ⟨hθx, hθx'⟩ := hswap x x' hx hx'
    have hCC : θ • (θ.symm • C) = C := smul_symm_smul θ C
    have hC₀inf : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) (θ.symm • C) :=
      ((hX (θ.symm • C)).2.2.2).mp (by rw [hCC]; exact hC)
    have h5 := ModularCurve.JHPlaceSpecialization.ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide p M H hpM A G hG x hx
      (θ.symm • C) hC₀inf
    have hsG : θ.symm G = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((p : AlgebraicClosure ℚ) ^ 12) * G⁻¹ :=
      symm_apply_eq_of_apply_eq θ G _ hc0 hG0 (hT G hG)
    have hsx' : θ.symm x' = x := by rw [θ.symm_apply_eq]; exact hθx.symm
    have e1 : C.ord G = (θ.symm • C).ord (θ.symm G) := by
      conv_lhs => rw [← hCC]
      exact ord_algEquiv_smul θ _ G
    have e2 : C.ord x' = (θ.symm • C).ord x := by
      conv_lhs => rw [← hCC]
      rw [ord_algEquiv_smul θ _ x', hsx']
    rw [e1, e2, hsG, Place.ord_mul _ ((map_ne_zero_iff _ (algebraMap _ _).injective).mpr hc0) (inv_ne_zero hG0),
      Place.ord_algebraMap, Place.ord_inv, zero_add, h5, hm]

end S_ModularCurve_XHDRModelAtP_exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen (solution)
