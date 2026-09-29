-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.reduceSnd_ofAlgAut_symm_smul_eq_reduceFst_and_isStrictSnd_iff_isStrictFst_ofAlgAut_symm_smul_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a2cd4dbc-10d5-542f-9f2e-1b54a2762f04

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_XHDRModelAtP_ofAlgAut_smul_ofAlgAut_smul_eq_ofAlgAut_diamondAutHBar_inv_smul_of_unitsMap_mul_eq_one_prolongationDatum
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum_all
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_reduceSnd_ofAlgAut_symm_smul_eq_reduceFst_and_isStrictSnd_iff_isStrictFst_ofAlgAut_symm_smul_prolongationDatum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option maxHeartbeats 16000000 in
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
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
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (SemilinearAut.ofAlgAut θ.symm • W) = Psp.reduceFst α hα W ∧
    (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ↔ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (SemilinearAut.ofAlgAut θ.symm • W)) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp := (Fact.out : p.Prime)

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    rw [pow_two, ← Nat.mul_div_cancel' hpM]
    exact Nat.mul_dvd_mul_left p h

  set g : SemilinearAut (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) with hgdef
  have hδg : ∀ v, δ v = g • v := fun v => hδ v

  have hT1 : ∀ X : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ X = δ (Psp.reduceFst α hα (SemilinearAut.ofAlgAut θ.symm • X)) := by
    intro X
    unfold JHPlaceSpecialization.reduceSnd JHPlaceSpecialization.reduceFst
    congr 2
    have h := AlgebraicCurve.Place.smul_restrictAlong α (θ.toAlgHom.comp α) hα hβ θ.symm 1 (fun x => by
      change α x = θ.symm (θ (α x)); rw [AlgEquiv.symm_apply_apply]) X
    rw [one_smul] at h
    exact h.symm

  obtain ⟨d, hdlift⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) pb⁻¹
  have hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
    rw [hdlift, ← hpb, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hWSQ : ∀ X : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ • X) = (SemilinearAut.ofAlgAut (diamondAutHBar M H d))⁻¹ • X := fun X =>
    ModularCurve.XHDRModelAtP.ofAlgAut_smul_ofAlgAut_smul_eq_ofAlgAut_diamondAutHBar_inv_smul_of_unitsMap_mul_eq_one_prolongationDatum
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat d hd X
  have hθsymm : ∀ X : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      SemilinearAut.ofAlgAut θ.symm • (SemilinearAut.ofAlgAut θ.symm • X) = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • X := by
    intro X
    have h := hWSQ (SemilinearAut.ofAlgAut θ.symm • (SemilinearAut.ofAlgAut θ.symm • X))
    have hinv : SemilinearAut.ofAlgAut θ.symm = (SemilinearAut.ofAlgAut θ)⁻¹ := by
      rw [← map_inv]; rfl
    rw [hinv, smul_inv_smul, smul_inv_smul] at h
    rw [hinv]
    conv_rhs => rw [h]
    rw [smul_inv_smul]

  have key : ∀ X : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα (SemilinearAut.ofAlgAut (diamondAutHBar M H d) • X) =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • Psp.reduceFst α hα X := by
    intro X
    have hX : 𝔛.Meta.pointEquivPlace (𝔛.Meta.pointEquivPlace.symm X) = X := Equiv.apply_symm_apply _ X

    obtain ⟨u, hu, uκ, huκ₁, huκ₂, i, P0, hP0⟩ :=
      ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
        p M H hpM hj 𝔛 A hA ρ hρ (𝔛.Meta.pointEquivPlace.symm X)

    have hDR := ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum_all
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat d i
      (𝔛.Meta.pointEquivPlace.symm X) u hu uκ huκ₁ huκ₂ P0 hP0

    have hφe : ∀ (e : (ZMod (M / p))ˣ) (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
        qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e)) • v) =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e)) • qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v := fun e v =>
      ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) e) v
    fin_cases i
    ·
      have h := hDR.1 rfl
      rw [hX] at h
      exact h
    ·
      have hrdF := hcompat' 1 (𝔛.Meta.pointEquivPlace.symm X) u hu uκ huκ₁ huκ₂ P0 hP0
      have hrdS := hcompat 1 (𝔛.Meta.pointEquivPlace.symm X) u hu uκ huκ₁ huκ₂ P0 hP0
      rw [if_neg (by decide)] at hrdF hrdS
      rw [hX] at hrdF hrdS
      have hS := hDR.2 rfl
      rw [hX] at hS

      set X' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := SemilinearAut.ofAlgAut (diamondAutHBar M H d) • X with hX'def
      have hX' : 𝔛.Meta.pointEquivPlace (𝔛.Meta.pointEquivPlace.symm X') = X' := Equiv.apply_symm_apply _ X'
      obtain ⟨u', hu', uκ', huκ'₁, huκ'₂, i', P0', hP0'⟩ :=
        ModularCurve.XHDRModelAtP.exists_schemeHomOver_barPt_eq_and_fibre_lift_and_comp_base_closedPoint_eq
          p M H hpM hj 𝔛 A hA ρ hρ (𝔛.Meta.pointEquivPlace.symm X')
      fin_cases i'
      ·
        have hDR' := ModularCurve.XHDRModelAtP.reduceFst_smul_diamondAutHBar_eq_and_reduceSnd_smul_eq_of_section_comp_prolongationDatum_all
          p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat d⁻¹ 0
          (𝔛.Meta.pointEquivPlace.symm X') u' hu' uκ' huκ'₁ huκ'₂ P0' hP0'
        have h := hDR'.1 rfl
        rw [hX'] at h

        have hAH := ModularCurve.diamondAutHBar_mul_and_diamondAutHBar_one M H
        have hback : SemilinearAut.ofAlgAut (diamondAutHBar M H d⁻¹) • X' = X := by
          rw [hX'def, ← mul_smul, ← map_mul, ← hAH.1, inv_mul_cancel, hAH.2, map_one, one_smul]
        rw [hback, map_inv] at h

        have hGL := ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        have h2 := congrArg (fun v => SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))) • v) h
        beta_reduce at h2
        rw [(hGL.2.2.2.2.2.2 _ _ (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).1] at h2
        exact h2.symm
      ·
        have hrdF' := hcompat' 1 (𝔛.Meta.pointEquivPlace.symm X') u' hu' uκ' huκ'₁ huκ'₂ P0' hP0'
        have hrdS' := hcompat 1 (𝔛.Meta.pointEquivPlace.symm X') u' hu' uκ' huκ'₁ huκ'₂ P0' hP0'
        rw [if_neg (by decide)] at hrdF' hrdS'
        rw [hX'] at hrdF' hrdS'

        refine hrdF'.trans ?_
        rw [hrdS', hS, hφe, ← hrdS, ← hrdF]

  have hGL := ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
  have hi : Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (SemilinearAut.ofAlgAut θ.symm • W) = Psp.reduceFst α hα W := by
    rw [hT1, hθsymm, key, hδg, hdlift]
    exact ((hGL.2.2.2.2.2.2) _ (Psp.reduceFst α hα W) pb).1
  refine ⟨hi, ?_⟩

  have hφg : ∀ v, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (g • v) =
      g • qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v := fun v =>
    ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb) v
  have hφginv : ∀ v, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (g⁻¹ • v) =
      g⁻¹ • qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v := by
    intro v
    have : g⁻¹ = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)⁻¹) := by
      rw [hgdef, map_inv (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)) (CuspForm.gammaLift (M / p) pb),
        map_inv (SemilinearAut.ofAlgAut (K := ResidueField ↥A) (F := JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))]
    rw [this]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)⁻¹ v

  have hr₁ : Psp.reduceFst α hα (SemilinearAut.ofAlgAut θ.symm • W) = g⁻¹ • Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W := by
    rw [hT1 W, hδg, inv_smul_smul]
  unfold JHPlaceSpecialization.IsStrictSnd JHPlaceSpecialization.IsStrictFst JHPlaceSpecialization.Fixed
  rw [hi, hr₁]
  simp only [hδg, hφg, hφginv, smul_inv_smul, smul_eq_iff_eq_inv_smul]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩

end S_ModularCurve_XHDRModelAtP_reduceSnd_ofAlgAut_symm_smul_eq_reduceFst_and_isStrictSnd_iff_isStrictFst_ofAlgAut_symm_smul_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_reduceSnd_ofAlgAut_symm_smul_eq_reduceFst_and_isStrictSnd_iff_isStrictFst_ofAlgAut_symm_smul_prolongationDatum (solution)
