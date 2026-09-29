-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_originChart_fst_of_forall_ringHom_eq_zero_iff_mem_nonunits_of_tatePoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1eba6cf9-16a5-53ff-a59f-2fa2a4764eae

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassProjModel_kwZeroSect_comp_projMap_of_isVariableChangeHom
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_or_exists_reducesToOrigin
import Theorems.Thm_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits
import Theorems.Thm_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_and_reduceHom_vcFun_eq
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin
import Theorems.Thm_ValuationSubring_mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_act_of_isSectionTransport
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_map_of_comp_projMap_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_ReduceHom
import Theorems.Thm_ModularCurve_coeff_tateToricPoint_mem_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_originChart_fst_of_forall_ringHom_eq_zero_iff_mem_nonunits_of_tatePoint

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical
open CategoryTheory AlgebraicGeometry

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

section GPOKit
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GaussPOriginAux

theorem originChartι_comp_projModelStrCR {T : Type} [CommRing T] (W : WeierstrassCurve.Projective T) :
    originChartι W ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom ((fromZeroRingHom (projModelGradingCR W) _).comp
        (algebraMap T ((projModelGradingCR W) 0)))) := by
  show Proj.awayι (projModelGradingCR W) (coord W 1) (coord_mem W 1) one_pos ≫ projModelStrCR W = _
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem comp_scalar_eq {T Ω : Type} [CommRing T] [CommRing Ω] (W : WeierstrassCurve.Projective T)
    (pt : Spec (CommRingCat.of Ω) ⟶ projModelCR W) (g : T →+* Ω)
    (hpt : pt ≫ projModelStrCR W = Spec.map (CommRingCat.ofHom g))
    (χ : OriginChartRing W →+* Ω) (hχ : pt = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W) :
    χ.comp ((fromZeroRingHom (projModelGradingCR W) _).comp (algebraMap T ((projModelGradingCR W) 0))) = g := by
  have e : Spec.map (CommRingCat.ofHom (χ.comp ((fromZeroRingHom (projModelGradingCR W) _).comp
      (algebraMap T ((projModelGradingCR W) 0))))) = Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← originChartι_comp_projModelStrCR, ← Category.assoc, ← hχ, hpt]
  have h := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  simpa only [CommRingCat.hom_ofHom] using h

theorem point_originAt_iff_eq_zero {T Ω : Type} [CommRing T] [CommRing Ω] (W : WeierstrassCurve T)
    (pt : Spec (CommRingCat.of Ω) ⟶ projModelCR W.toProjective) (g : T →+* Ω)
    (hpt : pt ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom g)) :
    (∃ χ : OriginChartRing W.toProjective →+* Ω,
        pt = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W.toProjective ∧
          χ (xOverY W.toProjective) = 0 ∧ χ (zOverY W.toProjective) = 0) ↔
      pt = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W).1 := by
  obtain ⟨hO, hOx, hOz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 = Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  constructor
  · rintro ⟨χ, hχ, hx, hz⟩
    have heq : χ = g.comp (kwYChartEval T W) := by
      refine WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W _ _ (fun t => ?_) ?_ ?_
      · have h1 := comp_scalar_eq W.toProjective _ g hpt χ hχ
        have h2 := comp_scalar_eq W.toProjective _ (RingHom.id T) (by rw [(kwZeroSect T W).2, CommRingCat.ofHom_id, Spec.map_id]) (kwYChartEval T W) hO'
        have e1 := RingHom.congr_fun h1 t
        have e2 := RingHom.congr_fun h2 t
        simp only [RingHom.comp_apply, RingHom.id_apply] at e1 e2 ⊢
        rw [e1, e2]
      · show χ (xOverY W.toProjective) = g (kwYChartEval T W (xOverY W.toProjective))
        rw [hx, hOx, map_zero]
      · show χ (zOverY W.toProjective) = g (kwYChartEval T W (zOverY W.toProjective))
        rw [hz, hOz, map_zero]
    rw [hχ, hO', heq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · intro h
    refine ⟨g.comp (kwYChartEval T W), ?_, ?_, ?_⟩
    · rw [h, hO', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [RingHom.comp_apply, hOx, map_zero]
    · rw [RingHom.comp_apply, hOz, map_zero]

theorem originAt_iff_eq_zero {T Ω : Type} [CommRing T] [CommRing Ω] (W : WeierstrassCurve T) (P : Section W.toProjective)
    (g : T →+* Ω) :
    (∃ χ : OriginChartRing W.toProjective →+* Ω,
        Spec.map (CommRingCat.ofHom g) ≫ P.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W.toProjective ∧
          χ (xOverY W.toProjective) = 0 ∧ χ (zOverY W.toProjective) = 0) ↔
      Spec.map (CommRingCat.ofHom g) ≫ P.1 = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W).1 :=
  point_originAt_iff_eq_zero W _ g (by rw [Category.assoc, P.2, Category.comp_id])

theorem eq_zero_comp {T Ω Ω' : Type} [CommRing T] [CommRing Ω] [CommRing Ω'] (W : WeierstrassCurve T)
    (P : Section W.toProjective) (g : T →+* Ω) (h : Ω →+* Ω')
    (hP : Spec.map (CommRingCat.ofHom g) ≫ P.1 = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W).1) :
    Spec.map (CommRingCat.ofHom (h.comp g)) ≫ P.1 = Spec.map (CommRingCat.ofHom (h.comp g)) ≫ (kwZeroSect T W).1 := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hP, Category.assoc]

theorem isPullback_and_zero_of_eq {T T' : Type} [CommRing T] [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T)
    (W' : WeierstrassCurve T') (e : W' = W.map f)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map f).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective f φ) :
    IsPullback (eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)) ≫ Proj.map φ hφ)
        (projModelStrCR W'.toProjective) (projModelStrCR W.toProjective) (Spec.map (CommRingCat.ofHom f)) ∧
      (kwZeroSect T' W').1 ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)) ≫ Proj.map φ hφ =
        Spec.map (CommRingCat.ofHom f) ≫ (kwZeroSect T W).1 := by
  subst e
  simp only [eqToHom_refl, Category.id_comp]
  refine ⟨WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W.toProjective f φ hφ hcoef, ?_⟩
  obtain ⟨hχ, hx, hz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  obtain ⟨hχ', hx', hz'⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval (W.map f).toProjective
  exact WeierstrassCurve.DrinfeldGlobal.comp_projMap_eq_of_isOriginChartSection W.toProjective f φ hφ hcoef
    (kwZeroSect T W) (kwZeroSect T' (W.map f)) _ hχ hx hz _ hχ' hx' hz'

theorem baseChange_eq_zero {T T' Ω : Type} [CommRing T] [CommRing T'] [CommRing Ω] (f : T →+* T') (W : WeierstrassCurve T)
    (W' : WeierstrassCurve T') (e : W' = W.map f)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map f).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective f φ)
    (P : Section W.toProjective) (P' : Section W'.toProjective)
    (hPP' : P'.1 ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)) ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ P.1)
    (g : T' →+* Ω)
    (hP : Spec.map (CommRingCat.ofHom (g.comp f)) ≫ P.1 = Spec.map (CommRingCat.ofHom (g.comp f)) ≫ (kwZeroSect T W).1) :
    Spec.map (CommRingCat.ofHom g) ≫ P'.1 = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T' W').1 := by
  obtain ⟨hpb, hzero⟩ := isPullback_and_zero_of_eq f W W' e φ hφ hcoef
  apply hpb.hom_ext
  · rw [Category.assoc, hPP', Category.assoc, hzero, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hP]
  · rw [Category.assoc, P'.2, Category.assoc, (kwZeroSect T' W').2]

theorem act_eq_zero_iff {T Ω : Type} [CommRing T] [CommRing Ω] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (W' : WeierstrassCurve T) (e : W' = C • W)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hvc : IsVariableChangeHom W.toProjective C φ) [IsIso (Proj.map φ hφ)]
    (P : Section W.toProjective) (P' : Section W'.toProjective)
    (hPP' : P'.1 ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)) ≫ Proj.map φ hφ = P.1)
    (g : T →+* Ω) :
    Spec.map (CommRingCat.ofHom g) ≫ P'.1 = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W').1 ↔
      Spec.map (CommRingCat.ofHom g) ≫ P.1 = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W).1 := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at hPP'
  have hzero := WeierstrassProjModel.kwZeroSect_comp_projMap_of_isVariableChangeHom W C φ hφ hvc
  constructor
  · intro h
    rw [← hPP', ← hzero, ← Category.assoc, h, Category.assoc]
  · intro h
    rw [← cancel_mono (Proj.map φ hφ), Category.assoc, hPP', Category.assoc, hzero]
    exact h

theorem originAt_of_isOriginChartSection {T Ω : Type} [CommRing T] [CommRing Ω] (W : WeierstrassCurve.Projective T)
    (P : Section W) (χ : OriginChartRing W →+* T) (hχ : IsOriginChartSection P χ) (g : T →+* Ω)
    (hx : g (χ (xOverY W)) = 0) (hz : g (χ (zOverY W)) = 0) :
    ∃ χ' : OriginChartRing W →+* Ω,
      Spec.map (CommRingCat.ofHom g) ≫ P.1 = Spec.map (CommRingCat.ofHom χ') ≫ originChartι W ∧
        χ' (xOverY W) = 0 ∧ χ' (zOverY W) = 0 := by
  refine ⟨g.comp χ, ?_, hx, hz⟩
  have h : P.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W := hχ
  rw [h, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_originChartι_comp_projMap
    {T T' : Type} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ) :
    ∃ a : OriginChartRing W →+* OriginChartRing (W.map f),
      originChartι (W.map f) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom a) ≫ originChartι W ∧
      a (xOverY W) = xOverY (W.map f) ∧ a (zOverY W) = zOverY (W.map f) := by
  obtain ⟨-, hX⟩ := hcoef
  have key : ∀ (s : ProjModelRingCR (W.map f)) (hs : s ∈ projModelGradingCR (W.map f) 1)
      (e : φ (coord W 1) = s),
      ∃ a : OriginChartRing W →+* Away (projModelGradingCR (W.map f)) s,
        Proj.awayι (projModelGradingCR (W.map f)) s hs one_pos ≫ Proj.map φ hφ =
          Spec.map (CommRingCat.ofHom a) ≫ originChartι W ∧
        a (xOverY W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 0)
          (by simpa using coord_mem (W.map f) 0) ∧
        a (zOverY W) = Away.mk (projModelGradingCR (W.map f)) hs 1 (coord (W.map f) 2)
          (by simpa using coord_mem (W.map f) 2) := by
    intro s hs e
    subst e
    refine ⟨Away.map φ (coord W 1), ?_, ?_, ?_⟩
    · exact Proj.awayι_comp_map φ hφ one_pos (coord W 1) (coord_mem W 1)
    · show Away.map φ (coord W 1) (Away.mk _ (coord_mem W 1) 1 (coord W 0) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 0
    · show Away.map φ (coord W 1) (Away.mk _ (coord_mem W 1) 1 (coord W 2) _) = _
      rw [Away.map_mk]
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk]
      congr 1
      · exact hX 2
  exact key (coord (W.map f) 1) (coord_mem (W.map f) 1) (hX 1)

theorem zero_not_mem_basicOpen {T Ω : Type} [CommRing T] [Field Ω] (W : WeierstrassCurve T) (g : T →+* Ω)
    (z : Spec (CommRingCat.of Ω)) :
    (Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W).1) z ∉
      Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2) := by
  obtain ⟨hO, -, hOz⟩ := WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval W.toProjective
  have hO' : (kwZeroSect T W).1 = Spec.map (CommRingCat.ofHom (kwYChartEval T W)) ≫ originChartι W.toProjective := hO
  intro hmem
  rw [hO', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage,
    Proj.awayι_preimage_basicOpen (projModelGradingCR W.toProjective) (f_deg := coord_mem W.toProjective 1) (hm := one_pos)
      (g_deg := coord_mem W.toProjective 2) (hm' := one_pos)] at hmem
  change PrimeSpectrum.comap (g.comp (kwYChartEval T W)) z ∈
    PrimeSpectrum.basicOpen (Away.isLocalizationElem (coord_mem W.toProjective 1) (coord_mem W.toProjective 2)) at hmem
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hmem
  have he : Away.isLocalizationElem (coord_mem W.toProjective 1) (coord_mem W.toProjective 2) = zOverY W.toProjective := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.isLocalizationElem, zOverY, Away.val_mk, pow_one]
  apply hmem
  rw [he, RingHom.comp_apply, hOz, map_zero]
  exact Ideal.zero_mem _

theorem mem_basicOpen_or_eq_zero {T Ω : Type} [CommRing T] [Field Ω] (W : WeierstrassCurve T) (g : T →+* Ω)
    (pt : Spec (CommRingCat.of Ω) ⟶ projModelCR W.toProjective)
    (hpt : pt ≫ projModelStrCR W.toProjective = Spec.map (CommRingCat.ofHom g)) :
    (∀ z, pt z ∈ Proj.basicOpen (projModelGradingCR W.toProjective) (coord W.toProjective 2)) ∨
      pt = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W).1 := by
  classical

  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom W.toProjective g
  have hpb := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom W.toProjective g φ hφ hcoef
  have w : pt ≫ projModelStrCR W.toProjective = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom g) := by rw [hpt, Category.id_comp]
  let S : Section (W.map g).toProjective := ⟨hpb.lift pt (𝟙 _) w, hpb.lift_snd _ _ _⟩
  have hS : S.1 ≫ Proj.map φ hφ = pt := hpb.lift_fst _ _ _
  rcases WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_or_exists_reducesToOrigin ((W.map g).toProjective) S with
    ⟨a, b, ρ, hρ, -, -⟩ | ⟨χ, hχ, hx, hz⟩
  · left
    intro z
    have hρ' : S.1 = Spec.map (CommRingCat.ofHom ρ) ≫ zChartι (W.map g).toProjective := hρ
    have h1 : (S.1 z) ∈ Proj.basicOpen (projModelGradingCR (W.map g).toProjective) (coord (W.map g).toProjective 2) := by
      rw [← Proj.opensRange_awayι _ (coord (W.map g).toProjective 2) (coord_mem _ 2) one_pos, Scheme.Hom.mem_opensRange]
      exact ⟨Spec.map (CommRingCat.ofHom ρ) z, by rw [← Scheme.Hom.comp_apply, ← hρ']⟩
    rw [← hS, Scheme.Hom.comp_apply]
    have hc : φ (coord W.toProjective 2) = coord (W.map g).toProjective 2 := hcoef.2 2
    rw [← hc, ← Proj.map_preimage_basicOpen φ hφ] at h1
    exact h1
  · right

    have hval : ∀ t : Ω, -t ∈ maximalIdeal Ω → t = 0 := by
      intro t ht
      have hn : ¬ IsUnit (-t) := (IsLocalRing.mem_maximalIdeal _).mp ht
      have : -t = 0 := by
        by_contra hne
        exact hn (isUnit_iff_ne_zero.mpr hne)
      exact neg_eq_zero.mp this
    have hx0 : χ (xOverY (W.map g).toProjective) = 0 := hval _ hx
    have hz0 : χ (zOverY (W.map g).toProjective) = 0 := hval _ hz
    obtain ⟨a, ha, hax, haz⟩ := exists_originChartι_comp_projMap W.toProjective g φ hφ hcoef
    have hχ' : S.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι (W.map g).toProjective := hχ
    refine (point_originAt_iff_eq_zero W pt g hpt).mp ⟨χ.comp a, ?_, ?_, ?_⟩
    · rw [← hS, hχ', Category.assoc, ha, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [RingHom.comp_apply, hax, hx0]
    · rw [RingHom.comp_apply, haz, hz0]

theorem eq_zero_of_eq_zero_comp {T Ω Ω' : Type} [CommRing T] [Field Ω] [Field Ω'] (W : WeierstrassCurve T)
    (P : Section W.toProjective) (g : T →+* Ω) (h : Ω →+* Ω')
    (hP : Spec.map (CommRingCat.ofHom (h.comp g)) ≫ P.1 = Spec.map (CommRingCat.ofHom (h.comp g)) ≫ (kwZeroSect T W).1) :
    Spec.map (CommRingCat.ofHom g) ≫ P.1 = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T W).1 := by
  rcases mem_basicOpen_or_eq_zero W g (Spec.map (CommRingCat.ofHom g) ≫ P.1) (by rw [Category.assoc, P.2, Category.comp_id]) with
    hZ | hO
  · exfalso
    obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of Ω')))
    have h1 := hZ (Spec.map (CommRingCat.ofHom h) z)
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hP] at h1
    exact zero_not_mem_basicOpen W (h.comp g) z h1
  · exact hO

end GaussPOriginAux

end GPOKit

namespace GPOAux

theorem one_sub_mem_maximalIdeal_of_pow_eq_one {R : Type*} [CommRing R] [IsLocalRing R] (q : ℕ) (hq : q.Prime)
    (hqR : (q : R) ∈ IsLocalRing.maximalIdeal R) (c : R) (hc : c ^ q = 1) :
    1 - c ∈ IsLocalRing.maximalIdeal R := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hqκ : (q : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact hqR
  haveI : CharP (IsLocalRing.ResidueField R) q := by
    rw [CharP.charP_iff_prime_eq_zero hq]; exact hqκ
  have h : (IsLocalRing.residue R c) ^ q = 1 := by rw [← map_pow, hc, map_one]
  have h2 : (IsLocalRing.residue R c - 1) ^ q = 0 := by rw [sub_pow_char, h, one_pow, sub_self]
  have h3 : IsLocalRing.residue R c - 1 = 0 := pow_eq_zero_iff (hq.ne_zero) |>.mp h2
  rw [map_sub, map_one, sub_eq_zero, eq_comm, ← sub_eq_zero]; exact h3

theorem mem_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L) (x : L) (n : ℕ) (hn : 0 < n)
    (hx : x ^ n = 1) : x ∈ A := by
  rcases A.mem_or_inv_mem x with h | h
  · exact h
  · have hx0 : x ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hx; exact zero_ne_one hx
    have : x = (x⁻¹) ^ (n - 1) := by
      have h1 : x * x ^ (n - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hn, hx]
      rw [inv_pow]; exact (eq_inv_of_mul_eq_one_left h1)
    rw [this]; exact A.pow_mem h _

theorem natCast_mem_maximalIdeal_comap (A : ValuationSubring (AlgebraicClosure ℚ))
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : ℕ)
    (hA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) :
    ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈
      IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by

  let φ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥A :=
    { toFun := fun a => ⟨algebraMap ↥k₀ (AlgebraicClosure ℚ) (a : ↥k₀), ValuationSubring.mem_comap.mp a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' : IsUnit ((q : ℕ) : ↥A) := by simpa using hu.map φ
  have hmem : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    push_cast; exact hA
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmem) hu'

theorem hahnSeries_C_mem {L : Type} [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (a : ↥A₀) : (HahnSeries.C (a : L) : LaurentSeries L) ∈ L₂ := by
  rw [hL₂]
  refine ⟨PowerSeries.C a, 1, one_ne_zero, ?_⟩
  rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]; rfl

theorem coe_mem_subfield_of_forall_mem_iff {L : Type} [Field L] (A₀ : ValuationSubring L)
    (K : IntermediateField L (LaurentSeries L)) (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (f : ↥K) : (f : LaurentSeries L) ∈ L₂ := by
  have key : ∀ g : ↥K, g ∈ W₀ → (g : LaurentSeries L) ∈ L₂ := by
    intro g hg
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ g).mp hg
    rw [hL₂]
    refine ⟨x, y, ?_, hxy⟩
    rintro rfl; exact hy (by rw [map_zero])
  rcases W₀.mem_or_inv_mem f with h | h
  · exact key f h
  · by_cases hf0 : f = 0
    · rw [hf0]; simp
    · have h1 := key f⁻¹ h
      have hcoe : ((f⁻¹ : ↥K) : LaurentSeries L) = ((f : ↥K) : LaurentSeries L)⁻¹ := by simp
      rw [hcoe] at h1
      simpa using L₂.inv_mem h1

theorem mem_of_coe_eq_C {L : Type} [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (W₂ : ValuationSubring ↥L₂)
    (hW₂ : ∀ f : ↥L₂, f ∈ W₂ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (a : ↥A₀) (f : ↥L₂) (hf : (f : LaurentSeries L) = HahnSeries.C (a : L)) : f ∈ W₂ := by
  rw [hW₂]
  refine ⟨PowerSeries.C a, 1, ?_, ?_⟩
  · rw [map_one]; exact one_ne_zero
  · rw [map_one, map_one, mul_one, hf, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]; rfl

theorem mem_of_coe_eq_C' {L : Type} [Field L] (A₀ : ValuationSubring L) (K : IntermediateField L (LaurentSeries L))
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (a : ↥A₀) (f : ↥K) (hf : (f : LaurentSeries L) = HahnSeries.C (a : L)) : f ∈ W₀ := by
  rw [hW₀]
  refine ⟨PowerSeries.C a, 1, ?_, ?_⟩
  · rw [map_one]; exact one_ne_zero
  · rw [map_one, map_one, mul_one, hf, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]; rfl

theorem coe_algebraMap_eq_C {L : Type} [Field L] (A₀ : ValuationSubring L) (K : IntermediateField L (LaurentSeries L))
    [Algebra ↥A₀ ↥K] [IsScalarTower ↥A₀ L ↥K] (a : ↥A₀) :
    ((algebraMap ↥A₀ ↥K a : ↥K) : LaurentSeries L) = HahnSeries.C (a : L) := by
  rw [IsScalarTower.algebraMap_apply ↥A₀ L ↥K]
  change algebraMap L (LaurentSeries L) (a : L) = HahnSeries.C (a : L)
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap L (PowerSeries L) (a : L) = PowerSeries.C (a : L) := by
    simp [PowerSeries.algebraMap_apply]
  rw [h1, HahnSeries.ofPowerSeries_C]

end GPOAux

section GPOMain
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GaussPOriginMain

def PZeroAt {T Ω : Type} [CommRing T] [CommRing Ω] (x : RawDrinfeldPair T) (g : T →+* Ω) : Prop :=
  Spec.map (CommRingCat.ofHom g) ≫ x.P.1 = Spec.map (CommRingCat.ofHom g) ≫ (kwZeroSect T x.curve).1

theorem pZeroAt_iff_exists {T Ω : Type} [CommRing T] [CommRing Ω] (x : RawDrinfeldPair T) (g : T →+* Ω) :
    PZeroAt x g ↔ ∃ χ : OriginChartRing x.curve →+* Ω,
      Spec.map (CommRingCat.ofHom g) ≫ x.P.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι x.curve ∧
        χ (xOverY x.curve) = 0 ∧ χ (zOverY x.curve) = 0 :=
  (GaussPOriginAux.originAt_iff_eq_zero x.curve x.P g).symm

theorem pZeroAt_comp {T Ω Ω' : Type} [CommRing T] [CommRing Ω] [CommRing Ω'] (x : RawDrinfeldPair T)
    (g : T →+* Ω) (h : Ω →+* Ω') (hx : PZeroAt x g) : PZeroAt x (h.comp g) :=
  GaussPOriginAux.eq_zero_comp x.curve x.P g h hx

theorem pZeroAt_of_comp {T Ω Ω' : Type} [CommRing T] [Field Ω] [Field Ω'] (x : RawDrinfeldPair T)
    (g : T →+* Ω) (h : Ω →+* Ω') (hx : PZeroAt x (h.comp g)) : PZeroAt x g :=
  GaussPOriginAux.eq_zero_of_eq_zero_comp x.curve x.P g h hx

theorem pZeroAt_act_iff {A : Type} [CommRing A] {𝒢 : GroupLaws A} {q : ℕ} (𝒯 : LevelTransport A 𝒢 q)
    (h𝒯 : 𝒯.IsSectionTransport) {T Ω : Type} [CommRing T] [Algebra A T] [CommRing Ω]
    (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T) (g : T →+* Ω) :
    PZeroAt (𝒯.act C x) g ↔ PZeroAt x g := by
  obtain ⟨hc, hsq⟩ := h𝒯.1 T C x
  obtain ⟨φ, hφ, hvc, hiso, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap x.curve C
  haveI := hiso
  exact GaussPOriginAux.act_eq_zero_iff x.curve C (𝒯.act C x).curve hc φ hφ hvc x.P (𝒯.act C x).P
    (hsq φ hφ hvc).1 g

theorem pZeroAt_map_of_comp {A : Type} [CommRing A] {𝒢 : GroupLaws A} {q : ℕ} (𝒯 : LevelTransport A 𝒢 q)
    (h𝒯 : 𝒯.IsSectionTransport) {T T' Ω : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing Ω]
    (f : T →ₐ[A] T') (x : RawDrinfeldPair T) (g : T' →+* Ω) (hx : PZeroAt x (g.comp f.toRingHom)) :
    PZeroAt (𝒯.map f x) g := by
  obtain ⟨hc, hsq⟩ := h𝒯.2 T T' f x
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom x.curve f.toRingHom
  exact GaussPOriginAux.baseChange_eq_zero f.toRingHom x.curve (𝒯.map f x).curve hc φ hφ hcoef x.P (𝒯.map f x).P
    (hsq φ hφ hcoef).1 g hx

theorem pZeroAt_comp_of_map {A : Type} [CommRing A] {𝒢 : GroupLaws A} {q : ℕ} (𝒯 : LevelTransport A 𝒢 q)
    (h𝒯 : 𝒯.IsSectionTransport) {T T' Ω : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing Ω]
    (f : T →ₐ[A] T') (x : RawDrinfeldPair T) (g : T' →+* Ω) (hx : PZeroAt (𝒯.map f x) g) :
    PZeroAt x (g.comp f.toRingHom) := by
  obtain ⟨hc, hsq⟩ := h𝒯.2 T T' f x
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom x.curve f.toRingHom
  obtain ⟨hpb, hzero⟩ := GaussPOriginAux.isPullback_and_zero_of_eq f.toRingHom x.curve (𝒯.map f x).curve hc φ hφ hcoef
  have hPP' := (hsq φ hφ hcoef).1
  unfold PZeroAt at hx ⊢
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, ← hPP', ← hzero,
    ← Category.assoc, hx, Category.assoc]

theorem isSectionThrough_map {A : Type} [CommRing A] {𝒢 : GroupLaws A} {q : ℕ} (𝒯 : LevelTransport A 𝒢 q)
    (h𝒯 : 𝒯.IsSectionTransport) {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') (x : RawDrinfeldPair T) (a b : T) (hP : IsSectionThrough x.P a b) :
    IsSectionThrough (𝒯.map f x).P (f a) (f b) := by
  obtain ⟨hc, hsq⟩ := h𝒯.2 T T' f x
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom x.curve f.toRingHom
  have hPP' := (hsq φ hφ hcoef).1

  have key : ∀ (W' : WeierstrassCurve.Projective T') (e : W' = x.curve.map f.toRingHom) (P' : Section W')
      (h : P'.1 ≫ eqToHom (congrArg projModelCR e) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.P.1),
      IsSectionThrough P' (f a) (f b) := by
    intro W' e P' h
    subst e
    simp only [eqToHom_refl, Category.id_comp] at h
    exact WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_comp_projMap_eq_of_isCoefficientHom x.curve f.toRingHom
      φ hφ hcoef x.P a b hP P' h
  exact key _ hc _ hPP'

theorem isSectionThrough_map_Q {A : Type} [CommRing A] {𝒢 : GroupLaws A} {q : ℕ} (𝒯 : LevelTransport A 𝒢 q)
    (h𝒯 : 𝒯.IsSectionTransport) {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') (x : RawDrinfeldPair T) (a b : T) (hQ : IsSectionThrough x.Q a b) :
    IsSectionThrough (𝒯.map f x).Q (f a) (f b) := by
  obtain ⟨hc, hsq⟩ := h𝒯.2 T T' f x
  obtain ⟨φ, hφ, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom x.curve f.toRingHom
  have hQQ' := (hsq φ hφ hcoef).2
  have key : ∀ (W' : WeierstrassCurve.Projective T') (e : W' = x.curve.map f.toRingHom) (Q' : Section W')
      (h : Q'.1 ≫ eqToHom (congrArg projModelCR e) ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ x.Q.1),
      IsSectionThrough Q' (f a) (f b) := by
    intro W' e Q' h
    subst e
    simp only [eqToHom_refl, Category.id_comp] at h
    exact WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_comp_projMap_eq_of_isCoefficientHom x.curve f.toRingHom
      φ hφ hcoef x.Q a b hQ Q' h
  exact key _ hc _ hQQ'

theorem pZeroAt_of_forall_eq_zero_iff {T Ω Ω' : Type} [CommRing T] [Field Ω] [Field Ω'] (x : RawDrinfeldPair T)
    (g : T →+* Ω) (g' : T →+* Ω') (hker : ∀ t, g t = 0 ↔ g' t = 0) (h : PZeroAt x g') : PZeroAt x g := by
  classical
  have hk : RingHom.ker g = RingHom.ker g' := by
    ext t; rw [RingHom.mem_ker, RingHom.mem_ker]; exact hker t
  haveI : (RingHom.ker g').IsPrime := RingHom.ker_isPrime g'
  let Q := T ⧸ RingHom.ker g'
  let F := FractionRing Q
  let g₀ : T →+* F := (algebraMap Q F).comp (Ideal.Quotient.mk (RingHom.ker g'))

  let g'bar : Q →+* Ω' := RingHom.kerLift g'
  have hg'bar : Function.Injective g'bar := RingHom.kerLift_injective g'
  let gbar : Q →+* Ω := (RingHom.kerLift g).comp (Ideal.quotEquivOfEq hk).symm.toRingHom
  have hgbar : Function.Injective gbar :=
    (RingHom.kerLift_injective g).comp (Ideal.quotEquivOfEq hk).symm.injective
  let h₁ : F →+* Ω' := IsFractionRing.lift hg'bar
  let h₂ : F →+* Ω := IsFractionRing.lift hgbar
  have e₁ : h₁.comp g₀ = g' := by
    ext t
    show IsFractionRing.lift hg'bar (algebraMap Q F (Ideal.Quotient.mk (RingHom.ker g') t)) = g' t
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have e₂ : h₂.comp g₀ = g := by
    ext t
    show IsFractionRing.lift hgbar (algebraMap Q F (Ideal.Quotient.mk (RingHom.ker g') t)) = g t
    rw [IsFractionRing.lift_algebraMap]
    show RingHom.kerLift g ((Ideal.quotEquivOfEq hk).symm (Ideal.Quotient.mk (RingHom.ker g') t)) = g t
    rw [Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
    rfl
  rw [← e₁] at h
  have h0 : PZeroAt x g₀ := pZeroAt_of_comp x g₀ h₁ h
  rw [← e₂]
  exact pZeroAt_comp x g₀ h₂ h0

end GaussPOriginMain
end GPOMain

section GPOBigRingW2
namespace GPOBigRing

open HahnSeries

theorem ofPowerSeries_map_mem (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) (x : PowerSeries ↥A₀) :
    HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)) ∈ L₂ := by
  rw [hL₂]
  refine ⟨x, 1, one_ne_zero, ?_⟩
  rw [map_one, map_one, mul_one]

theorem hahnSeries_C_mem_of_mem (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) (a : L) (ha : a ∈ A₀) : (HahnSeries.C a : LaurentSeries L) ∈ L₂ := by
  have h := ofPowerSeries_map_mem L A₀ L₂ hL₂ (PowerSeries.C (⟨a, ha⟩ : ↥A₀))
  rwa [PowerSeries.map_C, HahnSeries.ofPowerSeries_C] at h

theorem hahnSeries_C_mem_of_forall (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) (c : L) : (HahnSeries.C c : LaurentSeries L) ∈ L₂ := by
  rcases A₀.mem_or_inv_mem c with hc | hc
  · exact hahnSeries_C_mem_of_mem L A₀ L₂ hL₂ c hc
  · by_cases hc0 : c = 0
    · rw [hc0, HahnSeries.C_zero]; exact L₂.zero_mem
    · have h := hahnSeries_C_mem_of_mem L A₀ L₂ hL₂ c⁻¹ hc
      have : (HahnSeries.C c : LaurentSeries L) = (HahnSeries.C c⁻¹)⁻¹ := by
        rw [← map_inv₀, inv_inv]
      rw [this]
      exact L₂.inv_mem h

theorem single_one_one_mem (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) : (HahnSeries.single (1 : ℤ) (1 : L) : LaurentSeries L) ∈ L₂ := by
  have h := ofPowerSeries_map_mem L A₀ L₂ hL₂ PowerSeries.X
  rwa [PowerSeries.map_X, HahnSeries.ofPowerSeries_X] at h

theorem single_mem (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) (n : ℤ) (c : L) : (HahnSeries.single n c : LaurentSeries L) ∈ L₂ := by
  have hX : (HahnSeries.single (1 : ℤ) (1 : L) : LaurentSeries L) ∈ L₂ := single_one_one_mem L A₀ L₂ hL₂
  have hC : (HahnSeries.C c : LaurentSeries L) ∈ L₂ := hahnSeries_C_mem_of_forall L A₀ L₂ hL₂ c

  have hpow : ∀ m : ℕ, (HahnSeries.single (m : ℤ) (1 : L) : LaurentSeries L) = (HahnSeries.single (1 : ℤ) (1 : L)) ^ m := by
    intro m
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have hsingle : (HahnSeries.single n c : LaurentSeries L) = (HahnSeries.single (1 : ℤ) (1 : L)) ^ n * HahnSeries.C c := by
    rw [HahnSeries.C_apply]
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · rw [zpow_natCast, ← hpow, HahnSeries.single_mul_single, add_zero, one_mul]
    · rw [zpow_neg, zpow_natCast, ← hpow]
      have hinv : ((HahnSeries.single (m : ℤ) (1 : L) : LaurentSeries L))⁻¹ = HahnSeries.single (-(m : ℤ)) (1 : L) := by
        apply inv_eq_of_mul_eq_one_right
        rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, HahnSeries.single_zero_one]
      rw [hinv, HahnSeries.single_mul_single, add_zero, one_mul]
  rw [hsingle]
  exact L₂.mul_mem (L₂.zpow_mem hX n) hC

open HahnSeries

theorem ofPowerSeries_mem_of_forall_coeff_mem (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (P : PowerSeries L) (hP : ∀ n : ℕ, PowerSeries.coeff n P ∈ A₀) :
    HahnSeries.ofPowerSeries ℤ L P ∈ L₂ := by
  have e : P = (PowerSeries.mk fun n => (⟨PowerSeries.coeff n P, hP n⟩ : ↥A₀)).map (algebraMap ↥A₀ L) := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  rw [e]
  exact ofPowerSeries_map_mem L A₀ L₂ hL₂ _

theorem mem_of_mul_C_mem (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (x : LaurentSeries L) (d : L) (hd : d ≠ 0) (h : x * HahnSeries.C d ∈ L₂) : x ∈ L₂ := by
  have hC : (HahnSeries.C d : LaurentSeries L) ∈ L₂ := hahnSeries_C_mem_of_forall L A₀ L₂ hL₂ d
  have hC0 : (HahnSeries.C d : LaurentSeries L) ≠ 0 := by
    intro h0; exact hd (HahnSeries.C_injective (by rw [h0, HahnSeries.C_zero]))
  have : x = x * HahnSeries.C d * (HahnSeries.C d)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hC0, mul_one]
  rw [this]
  exact L₂.mul_mem h (L₂.inv_mem hC)

theorem tateToricPoint_mem (L : Type) [Field L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (p : ℕ) (c : Lˣ) (hc : (c : L) ∈ A₀) (hc' : ((c⁻¹ : Lˣ) : L) ∈ A₀) (hc1 : (c : L) ≠ 1) :
    (ModularCurve.tateToricPoint L p c).1 ∈ L₂ ∧ (ModularCurve.tateToricPoint L p c).2 ∈ L₂ := by
  obtain ⟨hpos, h0x, h0y, -⟩ := ModularCurve.coeff_tateToricPoint_mem_of_mem L p A₀.toSubring c hc hc'
  have hd : (1 - (c : L)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have hdA : (1 - (c : L)) ∈ A₀ := A₀.sub_mem A₀.one_mem hc
  have hunit : IsUnit (1 - (c : L)) := isUnit_iff_ne_zero.mpr hd
  have hinv : ∀ k : ℕ, Ring.inverse (1 - (c : L)) ^ k * (1 - (c : L)) ^ k = 1 := by
    intro k; rw [← mul_pow, Ring.inverse_mul_cancel _ hunit, one_pow]

  have key : ∀ (z : LaurentSeries L) (P : PowerSeries L), z = HahnSeries.ofPowerSeries ℤ L P →
      (∀ m : ℕ, 0 < m → z.coeff (m : ℤ) ∈ A₀.toSubring) → ∀ (a : L), a ∈ A₀ → ∀ k : ℕ,
      z.coeff 0 = a * Ring.inverse (1 - (c : L)) ^ k → z ∈ L₂ := by
    intro z P hz hzpos a ha k hz0
    apply mem_of_mul_C_mem L A₀ L₂ hL₂ z ((1 - (c : L)) ^ k) (pow_ne_zero _ hd)
    rw [hz, ← HahnSeries.ofPowerSeries_C, ← map_mul]
    apply ofPowerSeries_mem_of_forall_coeff_mem L A₀ L₂ hL₂
    intro n
    rw [PowerSeries.coeff_mul_C]
    have hcoef : PowerSeries.coeff n P = z.coeff (n : ℤ) := by rw [hz, HahnSeries.ofPowerSeries_apply_coeff]
    rw [hcoef]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, hz0, mul_assoc, hinv, mul_one]; exact ha
    · exact mul_mem ((A₀.mem_toSubring _).mp (hzpos n hn)) (pow_mem hdA k)
  refine ⟨key _ _ (ModularCurve.tateToricPoint_fst L p c) (fun m hm => (hpos m hm).1) (c : L) hc 2 h0x,
    key _ _ (ModularCurve.tateToricPoint_snd L p c) (fun m hm => (hpos m hm).2) ((c : L) ^ 2) (A₀.pow_mem hc 2) 3 h0y⟩

theorem coeff_tateToricPoint_fst_self (L : Type) [Field L] (p : ℕ) (hp : 0 < p) (c : Lˣ) :
    (ModularCurve.tateToricPoint L p c).1.coeff (p : ℤ) = (c : L) + ((c⁻¹ : Lˣ) : L) - 2 := by
  rw [ModularCurve.tateToricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_neg hp.ne']
  have h1 : (∑ d ∈ p.divisors, if p ∣ d then ((p / d : ℕ) : L) * ((c : L) ^ (p / d) + ((c⁻¹ : Lˣ) : L) ^ (p / d)) else 0) =
      (c : L) + ((c⁻¹ : Lˣ) : L) := by
    rw [Finset.sum_eq_single_of_mem p (Nat.mem_divisors_self p hp.ne')]
    · rw [if_pos (dvd_refl p), Nat.div_self hp]; simp
    · intro d hd hne
      rw [if_neg]
      intro hpd
      exact hne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) hpd)
  have h2 : (if p ∣ p then ∑ e ∈ (p / p).divisors, (e : L) else 0) = 1 := by
    rw [if_pos (dvd_refl p), Nat.div_self hp]; simp
  rw [h1, h2]; ring

theorem exists_variableChange_map_subtype_eq (L : Type) [Field L] [CharZero L] (A₀ : ValuationSubring L) (L₂ : Subfield (LaurentSeries L))
    (hL₂ : ∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
      f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L)))
    (p : ℕ) [NeZero p] (hp : 1 < p) (ξ : Lˣ) (hξA : (ξ : L) ∈ A₀) (hξA' : ((ξ⁻¹ : Lˣ) : L) ∈ A₀) (hξ1 : (ξ : L) ≠ 1)
    (Cv : WeierstrassCurve.VariableChange (LaurentSeries L))
    (h_i : ((Cv.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L p ξ ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L p ξ ![1, 0]).2 + (ModularCurve.cuspPoint L p ξ ![1, 0]).1 ∧
        Cv.r = HahnSeries.C (-(12 : L)⁻¹) ∧ Cv.s = HahnSeries.C (-(2 : L)⁻¹) ∧ Cv.t = HahnSeries.C ((24 : L)⁻¹)) :
    ∃ Cv₂ : WeierstrassCurve.VariableChange ↥L₂, Cv₂.map L₂.subtype = Cv := by
  obtain ⟨hu, hr, hs, ht⟩ := h_i
  haveI : Fact (1 < p) := ⟨hp⟩

  have hcusp : ModularCurve.cuspPoint L p ξ ![1, 0] = ModularCurve.tateToricPoint L p ξ := by
    rw [ModularCurve.cuspPoint_of_eq_zero ξ (by simp)]
    simp [ZMod.val_one]
  rw [hcusp] at hu
  obtain ⟨hx, hy⟩ := tateToricPoint_mem L A₀ L₂ hL₂ p ξ hξA hξA' hξ1

  have h2 : (2 : LaurentSeries L) ∈ L₂ := by exact_mod_cast natCast_mem L₂ 2
  have hf : 2 * (ModularCurve.tateToricPoint L p ξ).1 + HahnSeries.C ((6 : L)⁻¹) ∈ L₂ :=
    L₂.add_mem (L₂.mul_mem h2 hx) (hahnSeries_C_mem_of_forall L A₀ L₂ hL₂ _)
  have hg : 2 * (ModularCurve.tateToricPoint L p ξ).2 + (ModularCurve.tateToricPoint L p ξ).1 ∈ L₂ :=
    L₂.add_mem (L₂.mul_mem h2 hy) hx
  have hf0 : 2 * (ModularCurve.tateToricPoint L p ξ).1 + HahnSeries.C ((6 : L)⁻¹) ≠ 0 := by
    intro h0
    have hc := congrArg (fun z : LaurentSeries L => z.coeff (p : ℤ)) h0
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p)).ne'
    simp only [HahnSeries.coeff_add, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hp0,
      HahnSeries.coeff_zero, add_zero] at hc
    rw [show ((2 : LaurentSeries L) * (ModularCurve.tateToricPoint L p ξ).1).coeff (p : ℤ) = 2 * (ModularCurve.tateToricPoint L p ξ).1.coeff (p : ℤ) by
      rw [show (2 : LaurentSeries L) = HahnSeries.C (2 : L) by rw [map_ofNat], HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul],
      coeff_tateToricPoint_fst_self L p (Nat.pos_of_ne_zero (NeZero.ne p)) ξ] at hc

    have hξ0 : (ξ : L) ≠ 0 := ξ.ne_zero
    have hinv : ((ξ⁻¹ : Lˣ) : L) = (ξ : L)⁻¹ := Units.val_inv_eq_inv_val ξ
    rw [hinv] at hc
    have : ((ξ : L) - 1) ^ 2 = 0 := by
      have h' : (ξ : L) + (ξ : L)⁻¹ - 2 = 0 := by
        rcases mul_eq_zero.mp hc with h | h
        · exact absurd h two_ne_zero
        · exact h
      have := congrArg (fun z => z * (ξ : L)) h'
      field_simp at this
      linear_combination this
    exact hξ1 (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))

  have hu₂ : ((Cv.u : (LaurentSeries L)ˣ) : LaurentSeries L) ∈ L₂ := by
    have : ((Cv.u : (LaurentSeries L)ˣ) : LaurentSeries L) =
        (2 * (ModularCurve.tateToricPoint L p ξ).2 + (ModularCurve.tateToricPoint L p ξ).1) *
          (2 * (ModularCurve.tateToricPoint L p ξ).1 + HahnSeries.C ((6 : L)⁻¹))⁻¹ := by
      rw [← hu, mul_assoc, mul_inv_cancel₀ hf0, mul_one]
    rw [this]; exact L₂.mul_mem hg (L₂.inv_mem hf)
  have hu₂' : ((Cv.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ∈ L₂ := by
    rw [Units.val_inv_eq_inv_val]; exact L₂.inv_mem hu₂
  let u₂ : (↥L₂)ˣ := ⟨⟨_, hu₂⟩, ⟨_, hu₂'⟩, Subtype.ext (Units.mul_inv Cv.u), Subtype.ext (Units.inv_mul Cv.u)⟩
  refine ⟨⟨u₂, ⟨Cv.r, hr ▸ hahnSeries_C_mem_of_forall L A₀ L₂ hL₂ _⟩, ⟨Cv.s, hs ▸ hahnSeries_C_mem_of_forall L A₀ L₂ hL₂ _⟩,
    ⟨Cv.t, ht ▸ hahnSeries_C_mem_of_forall L A₀ L₂ hL₂ _⟩⟩, ?_⟩
  cases Cv with
  | mk u r s t =>
    simp only [WeierstrassCurve.VariableChange.map]
    congr 1

end GPOBigRing
end GPOBigRingW2

section GPOBigRingW3
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
namespace GPOBigRing

theorem comp_eq_comp_kwZeroSect_residue_of_isSectionThrough_of_inv_mem_nonunits'
    {F : Type} [Field F] (𝒱 : ValuationSubring F) (f : ↥𝒱 →+* F) (hf : ∀ a : ↥𝒱, f a = (a : F))
    (W : WeierstrassCurve ↥𝒱) (W' : WeierstrassCurve F) (e : W' = W.map f)
    (S : Section W.toProjective) (S' : Section W'.toProjective)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map f).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective f φ)
    (hSS' : S'.1 ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)) ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom f) ≫ S.1)
    (xt yt : F) (hS' : IsSectionThrough S' xt yt) (hyt : yt ≠ 0) (hyt' : yt⁻¹ ∈ 𝒱.nonunits) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝒱)) ≫ S.1 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝒱)) ≫ (kwZeroSect ↥𝒱 W).1 := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at hSS'
  rcases WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_or_exists_reducesToOrigin W.toProjective S with
    ⟨a, b, hab⟩ | ⟨χ, hχ, hz, hw⟩
  ·
    exfalso
    have hS'ab : IsSectionThrough S' (f a) (f b) :=
      WeierstrassCurve.DrinfeldGlobal.isSectionThrough_map_of_comp_projMap_eq_of_isCoefficientHom
        W.toProjective f φ hφ hcoef S a b hab S' hSS'
    obtain ⟨-, huniq⟩ :=
      WeierstrassCurve.DrinfeldGlobal.equation_iff_exists_isSectionThrough_and_eq_iff_of_isSectionThrough
        (W.map f).toProjective
    obtain ⟨-, hyb⟩ := (huniq S' S' xt yt _ _ hS' hS'ab).mp rfl
    have hyb' : yt = (b : F) := hyb.trans (hf b)

    have hinv𝒱 : yt⁻¹ ∈ 𝒱 := 𝒱.nonunits_le hyt'
    have hmax : (⟨yt⁻¹, hinv𝒱⟩ : ↥𝒱) ∈ maximalIdeal ↥𝒱 := (ValuationSubring.coe_mem_nonunits_iff).mp hyt'
    have hunit : IsUnit (⟨yt⁻¹, hinv𝒱⟩ : ↥𝒱) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨yt, hyb' ▸ b.2⟩, ?_⟩
      apply Subtype.ext
      show yt⁻¹ * yt = 1
      exact inv_mul_cancel₀ hyt
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hunit
  ·
    have hx : IsLocalRing.residue ↥𝒱 (χ (xOverY W.toProjective)) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      have := neg_mem hz
      simpa [originParam] using this
    have hz' : IsLocalRing.residue ↥𝒱 (χ (zOverY W.toProjective)) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      have := neg_mem hw
      simpa [originW] using this
    exact (GaussPOriginAux.originAt_iff_eq_zero W S (IsLocalRing.residue ↥𝒱)).mp
      (GaussPOriginAux.originAt_of_isOriginChartSection W.toProjective S χ hχ (IsLocalRing.residue ↥𝒱) hx hz')

theorem comp_eq_comp_kwZeroSect_residue_of_isSectionThrough_of_inv_mem_nonunits
    {F : Type} [Field F] (𝒱 : ValuationSubring F) (W : WeierstrassCurve ↥𝒱)
    (W' : WeierstrassCurve F) (e : W' = W.map 𝒱.subtype)
    (S : Section W.toProjective) (S' : Section W'.toProjective)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map 𝒱.subtype).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map 𝒱.subtype).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective 𝒱.subtype φ)
    (hSS' : S'.1 ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective e)) ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom 𝒱.subtype) ≫ S.1)
    (xt yt : F) (hS' : IsSectionThrough S' xt yt) (hyt : yt ≠ 0) (hyt' : yt⁻¹ ∈ 𝒱.nonunits) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝒱)) ≫ S.1 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝒱)) ≫ (kwZeroSect ↥𝒱 W).1 :=
  comp_eq_comp_kwZeroSect_residue_of_isSectionThrough_of_inv_mem_nonunits' 𝒱 𝒱.subtype (fun _ => rfl) W W' e S S' φ hφ hcoef
    hSS' xt yt hS' hyt hyt'

end GPOBigRing

namespace GPOBigRing

section ComponentLaws

variable {A : Type} [CommRing A] (ℓ M q : ℕ)
  (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D → ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
  (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
      ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
  (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q)

theorem level_snd_snd_act {T : Type} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (x : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).Raw T) :
    ((rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).act C x).level.2.2 = 𝒯.act C x.level.2.2 := rfl

theorem level_snd_snd_mapRing {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).Raw T) :
    ((rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).mapRing f x).level.2.2 = 𝒯.map f x.level.2.2 := rfl

theorem curve_act {T : Type} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (x : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).Raw T) :
    ((rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).act C x).curve = C • x.curve := rfl

theorem curve_mapRing {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).Raw T) :
    ((rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).mapRing f x).curve = x.curve.map f.toRingHom := rfl

end ComponentLaws

end GPOBigRing

namespace GPOBigRing

theorem comp_eq_comp_kwZeroSect_residue_of_tate_comparison
    {A : Type} [CommRing A] (ℓ M q : ℕ)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D → ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {F : Type} [Field F] [DecidableEq F] (𝒱 : ValuationSubring F) [DecidableEq (IsLocalRing.ResidueField ↥𝒱)]
    [Algebra A ↥𝒱] [Algebra A F] (val : ↥𝒱 →ₐ[A] F) (hval : val.toRingHom = 𝒱.subtype)
    (x𝕎 : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).Raw ↥𝒱) (rF : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).Raw F)
    (De : WeierstrassCurve.VariableChange F)
    (hrel : rF = (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).act De ((rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).mapRing val x𝕎))
    (T : WeierstrassCurve ↥𝒱) (hTΔ : (T.map (IsLocalRing.residue ↥𝒱)).Δ ≠ 0)
    (Cv₂ : WeierstrassCurve.VariableChange F) (hcurve : rF.curve = Cv₂ • T.map 𝒱.subtype)
    (D₁ : ModularCurve.LevelPData F)
    (hP : IsSectionThrough rF.level.2.2.P D₁.xP D₁.yP) (hQ : IsSectionThrough rF.level.2.2.Q D₁.xQ D₁.yQ)
    (hyt0 : (D₁.variableChange Cv₂⁻¹).yP ≠ 0) (hyt' : ((D₁.variableChange Cv₂⁻¹).yP)⁻¹ ∈ 𝒱.nonunits) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝒱)) ≫ x𝕎.level.2.2.P.1 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥𝒱)) ≫ (kwZeroSect ↥𝒱 x𝕎.level.2.2.curve).1 := by

  obtain ⟨hcW, hΔW, -⟩ := x𝕎.isLevel.2.2
  have hΔ1 : (x𝕎.curve.map (IsLocalRing.residue ↥𝒱)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]; exact (x𝕎.isUnit_Δ.map _).ne_zero

  have hC : (Cv₂⁻¹ * De) • x𝕎.curve.map 𝒱.subtype = T.map 𝒱.subtype := by
    have h1 : rF.curve = De • x𝕎.curve.map 𝒱.subtype := by
      rw [hrel, curve_act, curve_mapRing, hval]
    rw [mul_smul, ← h1, hcurve, inv_smul_smul]
  obtain ⟨C₀, hC₀T, hC₀map, -, -⟩ :=
    WeierstrassCurve.exists_variableChange_map_eq_and_reduceHom_vcFun_eq hΔ1 hTΔ (Cv₂⁻¹ * De) hC

  obtain ⟨hc1, hsq1⟩ := h𝒯.1 ↥𝒱 C₀ x𝕎.level.2.2
  obtain ⟨φ1, hφ1, hvc1, hiso1, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap x𝕎.level.2.2.curve C₀
  obtain ⟨hPP1, -⟩ := hsq1 φ1 hφ1 hvc1
  haveI := hiso1
  apply (GaussPOriginAux.act_eq_zero_iff x𝕎.level.2.2.curve C₀ (𝒯.act C₀ x𝕎.level.2.2).curve hc1 φ1 hφ1 hvc1
    x𝕎.level.2.2.P (𝒯.act C₀ x𝕎.level.2.2).P hPP1 (IsLocalRing.residue ↥𝒱)).mp

  have hraw : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).mapRing val ((rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).act C₀ x𝕎) = (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).act Cv₂⁻¹ rF := by
    rw [(rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).mapRing_act, hval, hC₀map, (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).act_mul, ← hrel]
  have hmapT : 𝒯.map val (𝒯.act C₀ x𝕎.level.2.2) = 𝒯.act Cv₂⁻¹ rF.level.2.2 := by
    have h := congrArg (fun z : (rigidDataPow A ℓ M q hℓ hM 𝒢 𝒯).Raw F => z.level.2.2) hraw
    simp only [level_snd_snd_mapRing, level_snd_snd_act] at h
    exact h

  obtain ⟨φ2, hφ2, hvc2, -, -⟩ := WeierstrassProjModel.exists_isVariableChangeHom_isIso_projMap rF.level.2.2.curve Cv₂⁻¹
  obtain ⟨hPt, -⟩ := WeierstrassCurve.DrinfeldGlobal.isSectionThrough_act_of_isSectionTransport A 𝒢 q 𝒯 h𝒯 Cv₂⁻¹ rF.level.2.2
    ⟨φ2, hφ2, hvc2⟩ D₁ hP hQ
  have hS' : IsSectionThrough (𝒯.map val (𝒯.act C₀ x𝕎.level.2.2)).P (D₁.variableChange Cv₂⁻¹).xP (D₁.variableChange Cv₂⁻¹).yP := by
    rw [hmapT]; exact hPt

  obtain ⟨hc2, hsq2⟩ := h𝒯.2 ↥𝒱 F val (𝒯.act C₀ x𝕎.level.2.2)
  obtain ⟨φ3, hφ3, hcoef3⟩ := WeierstrassProjModel.exists_isCoefficientHom (𝒯.act C₀ x𝕎.level.2.2).curve val.toRingHom
  obtain ⟨hSS3, -⟩ := hsq2 φ3 hφ3 hcoef3
  have hf : ∀ a : ↥𝒱, val.toRingHom a = (a : F) := fun a => by rw [hval]; rfl
  exact comp_eq_comp_kwZeroSect_residue_of_isSectionThrough_of_inv_mem_nonunits' 𝒱 val.toRingHom hf
    (𝒯.act C₀ x𝕎.level.2.2).curve (𝒯.map val (𝒯.act C₀ x𝕎.level.2.2)).curve hc2
    (𝒯.act C₀ x𝕎.level.2.2).P (𝒯.map val (𝒯.act C₀ x𝕎.level.2.2)).P φ3 hφ3 hcoef3 hSS3 _ _ hS' hyt0 hyt'

end GPOBigRing
end GPOBigRingW3

set_option maxHeartbeats 16000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (P₀ : LevelModuliPackageAbs ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x₀ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx₀ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries ↥k₀) = ModularCurve.jqNModC ↥k₀ (q * ℓ'))
    (clC : P₀.B₀ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
    (hclC : ∀ b : P₀.B₀, ((clC b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = P₀.classify x₀ b)
    (hμ : haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
      ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries ↥k₀)) (r : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw ↥K),
      (Quot.mk _ r : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x₀ ∧

      (((C.u : (LaurentSeries ↥k₀)ˣ) : LaurentSeries ↥k₀) * (2 * (ModularCurve.cuspPoint ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : ↥k₀)⁻¹)) =
          2 * (ModularCurve.cuspPoint ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : ↥k₀)⁻¹) ∧ C.s = HahnSeries.C (-(2 : ↥k₀)⁻¹) ∧ C.t = HahnSeries.C ((24 : ↥k₀)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries ↥k₀)) = C • ModularCurve.tateBase ↥k₀ (q * ℓ') ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : ↥k₀ →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries ↥k₀))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' (q * ℓ') (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries ↥k₀)) = (ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(q : ZMod (q * ℓ')), 0] ![0, -(q : ZMod (q * ℓ'))]).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).xP ∧
        (Py : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).yP ∧
        (Qx : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).xQ ∧
        (Qy : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy))
    (θ : (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →+* (ResidueField ↥A))
    (hθ : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), θ (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a) =
      IsLocalRing.residue ↥A ⟨((a : ↥k₀) : AlgebraicClosure ℚ), ValuationSubring.mem_comap.mp a.2⟩)  :
    ∀ (Ω : Type) [Field Ω] [DecidableEq Ω] [Algebra (ResidueField ↥A) Ω]
      (V : Place (ResidueField ↥A) Ω)
      (ρ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* ↥V.toValuationSubring)

      (W₀ : ValuationSubring ↥K)
      (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), y.map (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ≠ 0 ∧
          (f : LaurentSeries ↥k₀) * HahnSeries.ofPowerSeries ℤ ↥k₀ (y.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀))
            = HahnSeries.ofPowerSeries ℤ ↥k₀ (x.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)))
      (hker : ∀ h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), ((ρ h : ↥V.toValuationSubring) : Ω) = 0 ↔
          ((h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) ∈ W₀.nonunits),
      ∀ [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥V.toValuationSubring]
        (ρA : P₀.B₀ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥V.toValuationSubring) (hρA : ∀ b : P₀.B₀, ρA b = ρ (clC b))
        (xV : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw ↥V.toValuationSubring)
        (hxV : (Quot.mk _ xV : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt ↥V.toValuationSubring) = (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ρA P₀.univ),
        ∃ (χP : OriginChartRing (xV.level.2.2.curve) →+* Ω),
          Spec.map (CommRingCat.ofHom (algebraMap ↥V.toValuationSubring Ω)) ≫ (xV.level.2.2.P).1 =
            Spec.map (CommRingCat.ofHom χP) ≫ originChartι (xV.level.2.2.curve) ∧
          χP (xOverY (xV.level.2.2.curve)) = 0 ∧ χP (zOverY (xV.level.2.2.curve)) = 0 := by
  intro Ω _ _ _ V ρ W₀ hW₀ hker _ ρA hρA xV hxV
  haveI hNZ : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
  haveI := hdvr

  obtain ⟨L₂, W₂, hL₂, hW₂, hW₂'⟩ :=
    ModularCurve.exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing ↥k₀
      (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) hdvr
  obtain ⟨W₀', hW₀'p, hAW₀, -, hjW₀, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC _ ↥k₀ K hK
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) j hj
  have hW₀eq : W₀' = W₀ := by
    ext f
    rw [hW₀'p f, hW₀ f]
  subst hW₀eq
  have hCW₀ : ∀ s : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
      (s : ↥K) ∈ W₀' :=
    ModularCurve.coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin ↥k₀ K
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) j W₀' hAW₀ (fun P hP => (hjW₀ P hP).1)

  have hKL₂ : ∀ f : ↥K, (f : LaurentSeries ↥k₀) ∈ L₂ :=
    GPOAux.coe_mem_subfield_of_forall_mem_iff (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) K W₀' hW₀'p L₂ hL₂
  let eK : ↥K →+* ↥L₂ := (algebraMap ↥K (LaurentSeries ↥k₀)).codRestrict L₂ hKL₂
  have heK : ∀ f : ↥K, ((eK f : ↥L₂) : LaurentSeries ↥k₀) = (f : LaurentSeries ↥k₀) := fun _ => rfl
  have hWW : ∀ f : ↥K, f ∈ W₀' ↔ eK f ∈ W₂ := fun f => by
    rw [hW₀'p f, hW₂ (eK f), heK]
  have hnn : ∀ f : ↥K, f ∈ W₀'.nonunits ↔ eK f ∈ W₂.nonunits :=
    ValuationSubring.mem_nonunits_iff_map_mem_nonunits_of_forall_mem_iff ↥K ↥L₂ eK W₀' W₂ hWW
  letI algL₂ : Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥L₂ :=
    (eK.comp (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K)).toAlgebra
  let e : ↥K →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥L₂ := { toRingHom := eK, commutes' := fun _ => rfl }
  have hAW₂ : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
      eK (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K a) ∈ W₂ := fun a => (hWW _).1 (hAW₀ a)
  let iAW : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥W₂ :=
    (eK.comp (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K)).codRestrict W₂ hAW₂
  letI algW₂ : Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥W₂ := iAW.toAlgebra
  let W₂val : ↥W₂ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥L₂ :=
    { toRingHom := W₂.subtype, commutes' := fun _ => rfl }
  have hCW₂ : ∀ s : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
      eK (s : ↥K) ∈ W₂ := fun s => (hWW _).1 (hCW₀ s)
  let inclR : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* ↥W₂ :=
    (eK.comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.toRingHom).codRestrict
      W₂ hCW₂
  let incl₂ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)
      →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥W₂ :=
    { toRingHom := inclR, commutes' := fun a => Subtype.ext rfl }

  let ρ' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)
      →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥V.toValuationSubring :=
    { toRingHom := ρ
      commutes' := fun a => by
        have h1 := hρA (algebraMap _ P₀.B₀ a)
        rw [AlgHom.commutes, AlgHom.commutes] at h1
        exact h1.symm }
  have hρ' : ρA = ρ'.comp clC := AlgHom.ext fun b => hρA b
  obtain ⟨u₀, hu₀⟩ := Quot.exists_rep P₀.univ
  have hxV' : (Quot.mk _ ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing ρ'
        ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing clC u₀)) :
        (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt ↥V.toValuationSubring)
      = Quot.mk _ xV := by
    rw [hxV, hρ', ← hu₀]
    show _ = Quot.mk _ ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ρ'.comp clC) u₀)
    rw [ModularCurve.RigidWeierstrassData.mapRing_comp]
  obtain ⟨D', hD'⟩ := ModularCurve.RigidWeierstrassData.exists_eq_act_of_mk_eq_mk _ _ _ hxV'
  subst hD'

  rw [← GaussPOriginMain.pZeroAt_iff_exists]
  refine (GaussPOriginMain.pZeroAt_act_iff 𝒯 h𝒯 D' _ _).2 ?_
  refine GaussPOriginMain.pZeroAt_map_of_comp 𝒯 h𝒯 ρ' _ _ ?_

  refine GaussPOriginMain.pZeroAt_of_forall_eq_zero_iff _ _ ((IsLocalRing.residue ↥W₂).comp incl₂.toRingHom) ?_ ?_
  · intro t
    show ((ρ t : ↥V.toValuationSubring) : Ω) = 0 ↔ IsLocalRing.residue ↥W₂ (incl₂ t) = 0
    rw [hker t, hnn, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  ·
    refine GaussPOriginMain.pZeroAt_comp_of_map 𝒯 h𝒯 incl₂ _ _ ?_

    have hqℓpos : 0 < q * ℓ' := Nat.pos_of_ne_zero (NeZero.ne _)
    have hℓlt : ℓ' < q * ℓ' := by
      have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
      have hℓpos : 0 < ℓ' := (Fact.out : ℓ'.Prime).pos
      nlinarith
    have h1lt : 1 < q * ℓ' := lt_of_le_of_lt (Fact.out : ℓ'.Prime).one_lt.le hℓlt

    have hξk : ξ ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) :=
      GPOAux.mem_of_pow_eq_one _ ξ (q * ℓ') hqℓpos hξ.pow_eq_one
    have hξk' : ξ⁻¹ ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) :=
      GPOAux.mem_of_pow_eq_one _ ξ⁻¹ (q * ℓ') hqℓpos (by rw [inv_pow, hξ.pow_eq_one, inv_one])
    have hξ1 : ξ ≠ 1 := hξ.ne_one h1lt

    have hq𝔪 : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈
        IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) :=
      GPOAux.natCast_mem_maximalIdeal_comap A k₀ q hA
    have hcq : ((⟨ξ, hξk⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ^ ℓ') ^ q = 1 := by
      apply Subtype.ext
      push_cast
      rw [← pow_mul, mul_comm, hξ.pow_eq_one]
    have hcu : IsUnit ((⟨ξ, hξk⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ^ ℓ') :=
      IsUnit.of_pow_eq_one hcq (Fact.out : q.Prime).ne_zero
    have hc𝔪 : 1 - (hcu.unit : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈
        IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      rw [IsUnit.unit_spec]
      exact GPOAux.one_sub_mem_maximalIdeal_of_pow_eq_one q Fact.out hq𝔪 _ hcq
    have hc1 : ((hcu.unit : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) ≠ 1 := by
      rw [IsUnit.unit_spec]
      push_cast
      exact hξ.pow_ne_one_of_pos_of_lt (Fact.out : ℓ'.Prime).ne_zero hℓlt

    obtain ⟨⟨T, hTL, hTΔ⟩, ⟨xt, yt, hxt, hyt, hyt0, -, hyt'⟩⟩ :=
      ModularCurve.exists_tateBase_eq_map_and_tateToricPoint_mem_nonunits ↥k₀ (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
        L₂ W₂ hL₂ hW₂ hW₂' (q * ℓ') hcu.unit hc𝔪 hc1
    have hunits : (Units.map (↑(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).subtype) hcu.unit : (↥k₀)ˣ) =
        (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit ^ ℓ' := by
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      rfl

    obtain ⟨Cv, r, hr, h_i, hcurve, -, -, Px, Py, Qx, Qy, hPx, hPy, hQx, hQy, hP, hQ⟩ := hμ

    obtain ⟨Cv₂, hCv₂⟩ := GPOBigRing.exists_variableChange_map_subtype_eq ↥k₀ (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
      L₂ hL₂ (q * ℓ') h1lt _ hξk (by rw [Units.val_inv_eq_inv_val]; exact hξk') hξ1 Cv h_i

    have hxK : (Quot.mk _ ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing
          (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val
          ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing clC u₀)) :
          (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt ↥K)
        = Quot.mk _ r := by
      have hval : (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val.comp clC
          = P₀.classify x₀ := AlgHom.ext fun b => hclC b
      rw [← ModularCurve.RigidWeierstrassData.mapRing_comp, hval]
      show (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map
          (P₀.classify x₀) (Quot.mk _ u₀) = _
      rw [hu₀, P₀.map_classify, hr]
    obtain ⟨D, hD⟩ := ModularCurve.RigidWeierstrassData.exists_eq_act_of_mk_eq_mk _ _ _ hxK
    have heval : e.comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).val
        = W₂val.comp incl₂ := AlgHom.ext fun _ => Subtype.ext rfl
    have hrel : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing e r
        = (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).act
            (D.map e.toRingHom)
            ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing W₂val
              ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing incl₂
                ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing clC u₀))) := by
      rw [hD, ModularCurve.RigidWeierstrassData.mapRing_act, ← ModularCurve.RigidWeierstrassData.mapRing_comp, heval,
        ModularCurve.RigidWeierstrassData.mapRing_comp]

    have hsub : L₂.subtype.comp eK = algebraMap ↥K (LaurentSeries ↥k₀) := RingHom.ext fun _ => rfl
    have hcurveL : ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing e r).curve
        = Cv₂ • T.map W₂.subtype := by
      apply WeierstrassCurve.map_injective (f := L₂.subtype) Subtype.val_injective
      show (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing e r).curve).map L₂.subtype
        = (Cv₂ • T.map W₂.subtype).map L₂.subtype
      have hcm : ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing e r).curve
          = r.curve.map eK := rfl
      rw [hcm, WeierstrassCurve.map_map, ← WeierstrassCurve.map_variableChange, hCv₂, hTL, hsub, hcurve]

    have hP1 := GaussPOriginMain.isSectionThrough_map 𝒯 h𝒯 e r.level.2.2 Px Py hP
    have hQ1 := GaussPOriginMain.isSectionThrough_map_Q 𝒯 h𝒯 e r.level.2.2 Qx Qy hQ

    have hD₁ : ((⟨e Px, e Py, e Qx, e Qy⟩ : ModularCurve.LevelPData ↥L₂).variableChange Cv₂⁻¹).yP = yt := by
      apply Subtype.val_injective
      have hmap : ∀ (E : ModularCurve.LevelPData ↥L₂), ((E.yP : ↥L₂) : LaurentSeries ↥k₀) = (E.map L₂.subtype).yP := fun _ => rfl
      rw [hmap, ModularCurve.LevelPData.map_variableChange]
      have hinv : (Cv₂⁻¹).map L₂.subtype = Cv⁻¹ := by
        rw [← hCv₂]; exact map_inv (WeierstrassCurve.VariableChange.mapHom L₂.subtype) Cv₂
      rw [hinv]
      have hE : (⟨e Px, e Py, e Qx, e Qy⟩ : ModularCurve.LevelPData ↥L₂).map L₂.subtype =
          (ModularCurve.cuspData ↥k₀ (q * ℓ') (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero)).unit
            ![(ℓ' : ZMod (q * ℓ')), 0] ![0, -(ℓ' : ZMod (q * ℓ'))]).variableChange Cv := by
        apply ModularCurve.LevelPData.ext
        · exact hPx
        · exact hPy
        · exact hQx
        · exact hQy
      rw [hE, ← ModularCurve.LevelPData.variableChange_mul, inv_mul_cancel, ModularCurve.LevelPData.variableChange_one,
        ModularCurve.cuspData_yP, ModularCurve.cuspPoint_of_eq_zero _ (by simp), hyt, hunits]
      congr 2
      simp [ZMod.val_natCast_of_lt hℓlt]
    have hyt0' : ((⟨e Px, e Py, e Qx, e Qy⟩ : ModularCurve.LevelPData ↥L₂).variableChange Cv₂⁻¹).yP ≠ 0 := by
      rw [hD₁]; exact hyt0
    have hyt'' : (((⟨e Px, e Py, e Qx, e Qy⟩ : ModularCurve.LevelPData ↥L₂).variableChange Cv₂⁻¹).yP)⁻¹ ∈ W₂.nonunits := by
      rw [hD₁]; exact hyt'
    exact GPOBigRing.comp_eq_comp_kwZeroSect_residue_of_tate_comparison ℓ' M' q hℓ hM 𝒢 𝒯 h𝒯 W₂ W₂val rfl _ _ _ hrel T hTΔ Cv₂
      hcurveL (⟨e Px, e Py, e Qx, e Qy⟩ : ModularCurve.LevelPData ↥L₂) hP1 hQ1 hyt0' hyt''

end S_ModularCurve_FullLevel_exists_originChart_fst_of_forall_ringHom_eq_zero_iff_mem_nonunits_of_tatePoint
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_originChart_fst_of_forall_ringHom_eq_zero_iff_mem_nonunits_of_tatePoint (solution)
