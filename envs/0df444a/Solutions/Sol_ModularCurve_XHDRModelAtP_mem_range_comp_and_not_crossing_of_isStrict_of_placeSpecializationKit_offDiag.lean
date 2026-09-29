-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/86684469-5766-52a8-a625-d1167526b463

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
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
    :
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
        ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫
          pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
      (yκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : yκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1) (_ : yκ ≫ pullback.snd _ _ = 𝟙 _),
      (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V →
        yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        ¬ (yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
            yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base)) ∧
      (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V →
        yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base ∧
        ¬ (yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
            yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base)) := by
  intro V s hs yκ hy₁ hy₂
  classical
  have hp : p.Prime := Fact.out
  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [pow_two, mul_assoc, ← hk, mul_comm, Nat.div_mul_cancel hpM]⟩
  haveI : IsProper (toBase p (ΓM M H) hj) := 𝔛.isProper

  set pt := yκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) with hpt
  set y := (𝔛.Meta.pointEquivPlace).symm V with hy
  have hyV : 𝔛.Meta.pointEquivPlace y = V := Equiv.apply_symm_apply _ _
  have hs' : barPt A ≫ s.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := hs
  set r₁ := Psp.reduceFst α hα V with hr₁
  set r₂ := Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V with hr₂
  set φ := qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p with hφ

  have hptcl : IsClosed ({pt} : Set (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) := by
    have h1 : IsClosedImmersion (yκ ≫ pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) := by
      rw [hy₂]; infer_instance
    have h2 : IsClosedImmersion yκ := IsClosedImmersion.of_comp yκ (pullback.snd _ _)
    have hrange : Set.range yκ.base = {pt} := by
      ext z
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨w, rfl⟩; rw [hpt, Subsingleton.elim w (IsLocalRing.closedPoint _)]
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hrange]
    exact yκ.isClosedEmbedding.isClosed_range

  have hP : ∀ i : Fin 2, pt ∈ Set.range (𝔛.comp A hA ρ hρ i).base →
      ∃ P : closedPoints (𝔛.Mfib A hA ρ hρ).C, (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = pt := by
    rintro i ⟨q, hq⟩
    haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ i
    let x := (inv (𝔛.efib A hA ρ hρ)).base q
    have hx : (𝔛.efib A hA ρ hρ).base x = q := by
      show (inv (𝔛.efib A hA ρ hρ) ≫ 𝔛.efib A hA ρ hρ).base q = q
      rw [IsIso.inv_hom_id]; rfl
    have hxpt : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base x = pt := by
      rw [Scheme.Hom.comp_apply, hx, hq]
    refine ⟨⟨x, ?_⟩, hxpt⟩
    rw [mem_closedPoints_iff]
    have hinj : Function.Injective (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base :=
      (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).isClosedEmbedding.injective
    have heq : ({x} : Set _) = (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base ⁻¹' {pt} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hxpt
      · intro hz; exact hinj (hz.trans hxpt.symm)
    rw [heq]
    exact hptcl.preimage (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).continuous

  have h1ne : (1 : Fin 2) ≠ 0 := by decide
  have hA1 : pt ∈ Set.range (𝔛.comp A hA ρ hρ 1).base → r₁ = φ r₂ := by
    intro hmem
    obtain ⟨P, hPpt⟩ := hP 1 hmem
    have ha := hcompat 1 y s hs' yκ hy₁ hy₂ P hPpt
    have ha' := hcompat' 1 y s hs' yκ hy₁ hy₂ P hPpt
    rw [if_neg h1ne, hyV] at ha ha'
    rw [hr₁, ha', ha]
  have hA0 : pt ∈ Set.range (𝔛.comp A hA ρ hρ 0).base → r₂ = δ (φ r₁) := by
    intro hmem
    obtain ⟨P, hPpt⟩ := hP 0 hmem
    have ha := hcompat 0 y s hs' yκ hy₁ hy₂ P hPpt
    have ha' := hcompat' 0 y s hs' yκ hy₁ hy₂ P hPpt
    rw [if_pos rfl, hyV] at ha ha'
    rw [hr₂, ha', ha]

  have hδφ : ∀ v, φ (δ v) = δ (φ v) := by
    intro v
    rw [hδ, hδ]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v

  have hF1 : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → pt ∉ Set.range (𝔛.comp A hA ρ hρ 1).base := by
    rintro ⟨h1, hnf⟩ hmem
    have h1' : δ (φ r₁) = r₂ := h1
    apply hnf
    show φ (δ (φ r₁)) = r₁
    rw [h1', ← hA1 hmem]
  have hS0 : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → pt ∉ Set.range (𝔛.comp A hA ρ hρ 0).base := by
    rintro ⟨h2, hns⟩ hmem
    have h2' : r₁ = φ r₂ := h2
    apply hns
    show φ (δ (φ r₂)) = r₂
    rw [← h2', hδφ, ← hA0 hmem]
  have hcov := 𝔛.comp_jointly_surjective A hA ρ hρ pt
  refine ⟨fun hF => ?_, fun hS => ?_⟩
  · exact ⟨hcov.resolve_right (hF1 hF), fun h => hF1 hF h.2⟩
  · exact ⟨hcov.resolve_left (hS0 hS), fun h => hS0 hS h.1⟩

end S_ModularCurve_XHDRModelAtP_mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_mem_range_comp_and_not_crossing_of_isStrict_of_placeSpecializationKit_offDiag (solution)
