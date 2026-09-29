-- Prove2me | solution 1 for ModularCurve.exists_iso_xHDRLevel_top_drLevel_epsInf_pointEquivPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b1c0b684-cbbc-59e4-93ee-2a2dc5f7d89e

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
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_ModularCurve_exists_iso_igusaScheme_xHDRLevel_X_gammaH_top
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
import Theorems.Thm_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_iso_xHDRLevel_top_drLevel_epsInf_pointEquivPlace
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) [NeZero (N₀ * p)]
    (hpM : p ∣ N₀ * p) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj) (𝔓 : DRModelPackageLevel N₀ p hpN₀) :
    ∃ (hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p))
      (φ : XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj ≅ DRLevel.X N₀ p)
      (_ : φ.hom ≫ DRLevel.toBase N₀ p = XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
      (_ : 𝔛.εinf.1 ≫ φ.hom = 𝔓.εinf.1),
      (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
          (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ φ.hom = y₀.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ p) (genPt p) →
        𝔓.Meta.pointEquivPlace y₀ =
          Place.congrRingEquiv (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a)
            (𝔛.Meta.pointEquivPlace y)) := by

  have hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p) := by
    show laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionFieldC ℚ (N₀ * p) ⊤) = laurentBaseChange (AlgebraicClosure ℚ) _
    rw [xHFunctionFieldC_top, ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]

  obtain ⟨e, eFin, eInf, hFin, hInf, hbase, hcFin, hcInf⟩ :=
    ModularCurve.exists_iso_igusaScheme_xHDRLevel_X_gammaH_top p (N₀ * p) hj
  have hbase' : e.inv ≫ IgusaScheme.igusaTo (N₀ * p) p = XHDRLevel.toBase p (CohCarrier.GammaH (N₀ * p) ⊤) hj := by
    rw [← hbase, Iso.inv_hom_id_assoc]
  have hεinf : 𝔛.εinf.1 ≫ e.inv = 𝔓.εinf.1 := by
    have hρ : 𝔛.rhoInf.toRingHom.comp eInf = 𝔓.rhoInf.toRingHom := by
      apply RingHom.ext; intro b
      apply Subtype.ext
      show ((𝔛.rhoInf (eInf b) : XHDRLevel.R p) : ℚ) = ((𝔓.rhoInf b : XHDRLevel.R p) : ℚ)
      rw [𝔛.rhoInf_spec, 𝔓.rhoInf_spec, hInf]
    rw [𝔛.εinf_chart, Category.assoc, ← hcInf, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ, 𝔓.εinf_chart]

  let bQ := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))
  let m : pullback (XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj) bQ ⟶ pullback (DRLevel.toBase N₀ p) bQ :=
    pullback.map _ _ _ _ e.inv (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact hbase'.symm) (by rw [Category.comp_id, Category.id_comp])
  have hm₁ : m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e.inv := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝟙 _ := pullback.lift_snd _ _ _
  let ψ : 𝔛.Meta.C ⟶ 𝔓.Meta.C := 𝔛.eeta ≫ m ≫ inv 𝔓.eeta
  have hψ₁ : ψ ≫ 𝔓.eeta ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ≫ e.inv := by
    simp only [ψ, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hm₁]
  have hψ₂ : ψ ≫ 𝔓.Meta.toBase = 𝔛.Meta.toBase := by
    rw [← 𝔓.heeta, ← 𝔛.heeta]
    simp only [ψ, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [hm₂, Category.comp_id]
  haveI : IsIso ψ := by
    dsimp only [ψ, m]; infer_instance

  have hgen := ModularCurve.fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel N₀ p hpN₀ hpM hj 𝔛 𝔓 hF
    e eFin hFin hbase hcFin ψ hψ₁ hψ₂
  refine ⟨hF, e.symm, hbase', hεinf, ?_⟩
  intro y y₀ hy
  have hy₀ : y₀ = ⟨y.1 ≫ ψ, by rw [Category.assoc, hψ₂, y.2]⟩ := by
    apply Subtype.ext
    show y₀.1 = y.1 ≫ ψ
    rw [← cancel_mono 𝔓.eeta]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, hψ₁, ← hy]
      rfl
    · rw [Category.assoc, 𝔓.heeta, y₀.2, Category.assoc, Category.assoc, 𝔓.heeta, hψ₂, y.2]
  rw [hy₀]
  exact AlgebraicCurve.CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq 𝔛.Meta 𝔓.Meta
    (IntermediateField.equivOfEq hF).toRingEquiv (fun a => (IntermediateField.equivOfEq hF).commutes a) ψ hψ₂ hgen y

end S_ModularCurve_exists_iso_xHDRLevel_top_drLevel_epsInf_pointEquivPlace
end P2MW
export P2MW.S_ModularCurve_exists_iso_xHDRLevel_top_drLevel_epsInf_pointEquivPlace (solution)
