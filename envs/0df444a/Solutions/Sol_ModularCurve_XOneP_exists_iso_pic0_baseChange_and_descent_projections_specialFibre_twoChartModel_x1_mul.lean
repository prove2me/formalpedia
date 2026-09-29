-- Prove2me | solution 1 for ModularCurve.XOneP.exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/68a485d8-917a-5bfb-b00d-3da784264984

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_XOneP_exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_ModularCurve_XOneP_exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul.AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral Spec Spec.map Scheme Smooth IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RepresentsRelSubPic RelPicard.curveChange Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Modules.pullbackCongr Modules.pullbackId Modules residue Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso Modules.rigidify Modules.rigidifyMapIso Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext pullback pullbackCongr pullbackId pullbackComp IsInvertible pullbackUnitIso tensor dual dualMapIso rigidify rigidifyMapIso pullbackTensorObjIso pullbackTensorUnitObjIso IsInvertible.nonempty_iso_tensorUnit_of_field IsInvertible.nonempty_rigidify_pullback_tensor_iso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {T P T' P' : Scheme.{u}}

theorem nonempty_pullback_rigidify_iso {σ : T ⟶ P} {q : P ⟶ T} {σ' : T' ⟶ P'} {q' : P' ⟶ T'}
    (φ : P' ⟶ P) (g : T' ⟶ T) (hσ : σ' ≫ φ = g ≫ σ) (hq : φ ≫ q = q' ≫ g)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback φ).obj (rigidify σ q L) ≅
      rigidify σ' q' ((Scheme.Modules.pullback φ).obj L)) := by
  obtain ⟨d⟩ := (hL.pullback σ).pullback_dual g
  refine ⟨pullbackTensorObjIso φ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_)⟩
  exact (pullbackComp φ q).app _ ≪≫ (pullbackCongr hq).app _ ≪≫ ((pullbackComp q' g).app _).symm ≪≫
    (Scheme.Modules.pullback q').mapIso (d ≪≫ dualMapIso ((pullbackComp g σ).app L ≪≫
      (pullbackCongr hσ.symm).app L ≪≫ ((pullbackComp σ' φ).app L).symm))

def pullbackTensorPullbackIso {q : P ⟶ T} {q' : P' ⟶ T} (φ : P' ⟶ P) (hq : φ ≫ q = q')
    (N : P.Modules) (K : T.Modules) :
    (Scheme.Modules.pullback φ).obj (N ⊗ (Scheme.Modules.pullback q).obj K) ≅
      (Scheme.Modules.pullback φ).obj N ⊗ (Scheme.Modules.pullback q').obj K :=
  pullbackTensorObjIso φ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ((pullbackComp φ q).app K ≪≫ (pullbackCongr hq).app K))

theorem nonempty_rigidify_tensor_pullback_iso {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : P.Modules} (hN : Scheme.Modules.IsInvertible N) {K : T.Modules} (hK : Scheme.Modules.IsInvertible K) :
    Nonempty (rigidify σ q (N ⊗ (Scheme.Modules.pullback q).obj K) ≅ rigidify σ q N) :=
  ⟨rigidifyMapIso σ q (β_ _ _) ≪≫ (hK.nonempty_rigidify_pullback_tensor_iso hσq hN).some⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral Spec Spec.map Scheme Smooth IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RepresentsRelSubPic RelPicard.curveChange Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp baseChangeSnd_id rigSection_baseChangeSnd RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso FibrewiseAlgEquivZero.congr algEquivZeroCut curveChange curveChange_baseChangeSnd curveChange_snd FibrewiseAlgEquivZero.pullbackCurve RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify RepresentsRelSubPic.relativeGroupLaw algEquivZeroGroupCut BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst BaseChange.baseChangeSnd_fst' BaseChange.baseChangeSnd_snd' BaseChange.rigSection_κ_inv BaseChange.overR BaseChange.ofR BaseChange.toR_ofR_iso BaseChange.toR_pullbackAlong_iso BaseChange.fibrewiseAlgEquivZero_toR_iff rigSection_snd rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso RepresentsRelSubPic.existsUnique_hom_of_transform RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform"
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}

def ModAlgEquivZero (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : (Limits.pullback c t).Modules) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
    IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj L)

theorem fibrewiseAlgEquivZero_iff_mod {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) : FibrewiseAlgEquivZero M ↔ ModAlgEquivZero c t M.L := Iff.rfl

namespace ModAlgEquivZero

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

theorem of_iso {L L' : (Limits.pullback c t).Modules} (e : L ≅ L') (hL : ModAlgEquivZero c t L) :
    ModAlgEquivZero c t L' := fun k _ _ s => (hL k s).of_iso ((Scheme.Modules.pullback _).mapIso e)

theorem curveChange (f : C' ⟶ C) (hf : f ≫ c = c') {L : (Limits.pullback c t).Modules}
    (hL : ModAlgEquivZero c t L) :
    ModAlgEquivZero c' t ((Scheme.Modules.pullback (curveChange f hf t)).obj L) := by
  intro k _ _ s
  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (RelPicard.curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ RelPicard.curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hL k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm

theorem tensor_pullbackSnd {L : (Limits.pullback c t).Modules} (hL : ModAlgEquivZero c t L)
    {K : T.Modules} (hK : Scheme.Modules.IsInvertible K) :
    ModAlgEquivZero c t (L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj K) := by
  intro k _ _ s
  have triv : (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj
      ((Scheme.Modules.pullback (pullback.snd c t)).obj K) ≅ 𝟙_ _ :=
    (Scheme.Modules.pullbackComp _ _).app K ≪≫
      (Scheme.Modules.pullbackCongr (pullback.condition (f := pullback.snd c t) (g := s))).app K ≪≫
      ((Scheme.Modules.pullbackComp _ _).app K).symm ≪≫
      (Scheme.Modules.pullback _).mapIso
        (Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hK.pullback s)).some ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  refine (hL k s).of_iso ?_
  exact (ρ_ _).symm ≪≫ (Iso.refl _ ⊗ᵢ triv.symm) ≪≫ (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

theorem ofInvertible {L : (Limits.pullback c t).Modules} (hL' : Scheme.Modules.IsInvertible L)
    (hL : ModAlgEquivZero c t L) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε) L hL') :=
  hL.tensor_pullbackSnd ((hL'.pullback _).dual).1

end ModAlgEquivZero

def transportRigidify (f : C' ⟶ C) (hf : f ≫ c = c') (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  RigidifiedLineBundle.ofInvertible ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L)
    (M.isInvertible.pullback _)

namespace transportRigidify

variable (f : C' ⟶ C) (hf : f ≫ c = c') {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {t' : T' ⟶ Spec (CommRingCat.of R)}

theorem L_eq (M : RigidifiedLineBundle c ε t) :
    (transportRigidify f hf ε ε' t M).L = Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
      ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L) := rfl

theorem congr (M M' : RigidifiedLineBundle c ε t) (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((transportRigidify f hf ε ε' t M).L ≅ (transportRigidify f hf ε ε' t M').L) :=
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _ ((Scheme.Modules.pullback _).mapIso h.some)

theorem nat (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t) :
    Nonempty (((transportRigidify f hf ε ε' t M).pullbackAlong ψ).L ≅
      (transportRigidify f hf ε ε' t' (M.pullbackAlong ψ)).L) := by
  obtain ⟨e₁⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε') ψ
    ((M.isInvertible.pullback (curveChange f hf t)))
  refine ⟨e₁ ≪≫ (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _ ?_).some⟩
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd f hf ψ).symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

theorem cut (M : RigidifiedLineBundle c ε t) (hM : (algEquivZeroCut c ε).P t M) :
    (algEquivZeroCut c' ε').P t (transportRigidify f hf ε ε' t M) :=
  ModAlgEquivZero.ofInvertible _ (ModAlgEquivZero.curveChange f hf hM)

theorem tensor (M M' : RigidifiedLineBundle c ε t) :
    Nonempty ((transportRigidify f hf ε ε' t (M.tensor M')).L ≅
      ((transportRigidify f hf ε ε' t M).tensor (transportRigidify f hf ε ε' t M')).L) := by
  obtain ⟨e⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε')
    (M.isInvertible.pullback (curveChange f hf t)) (M'.isInvertible.pullback (curveChange f hf t))
  exact ⟨(RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _
    (Scheme.Modules.pullbackTensorObjIso _ _ _)).some ≪≫ e⟩

theorem unit (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((transportRigidify f hf ε ε' t (RigidifiedLineBundle.unit t)).L ≅
      (RigidifiedLineBundle.unit (c := c') (ε := ε') t).L) := by
  obtain ⟨e⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c') (ε := ε') t)
  exact ⟨(RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _
    (Scheme.Modules.pullbackUnitIso _)).some ≪≫ e⟩

theorem roundtrip (f' : C ⟶ C') (hf' : f' ≫ c' = c) (hff' : f' ≫ f = 𝟙 C) (M : RigidifiedLineBundle c ε t) :
    Nonempty ((transportRigidify f' hf' ε' ε t (transportRigidify f hf ε ε' t M)).L ≅ M.L) := by

  have hcc : curveChange f' hf' t ≫ curveChange f hf t = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      rw [hff', Category.comp_id]
    · simp only [curveChange, Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  have hK : Scheme.Modules.IsInvertible (rigCorrection ε' t ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L)) :=
    (((M.isInvertible.pullback _).pullback _).dual).1

  let e₁ : (Scheme.Modules.pullback (curveChange f' hf' t)).obj (transportRigidify f hf ε ε' t M).L ≅
      M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj
        (rigCorrection ε' t ((Scheme.Modules.pullback (curveChange f hf t)).obj M.L)) :=
    Scheme.Modules.pullbackTensorPullbackIso _ (curveChange_snd _ _ _) _ _ ≪≫
      (((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hcc).app _ ≪≫
        (Scheme.Modules.pullbackId _).app _) ⊗ᵢ Iso.refl _)
  obtain ⟨e₂⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((transportRigidify f hf ε ε' t M).isInvertible.pullback (curveChange f' hf' t))
    (M.isInvertible.tensor (hK.pullback _)) e₁
  obtain ⟨e₃⟩ := Scheme.Modules.nonempty_rigidify_tensor_pullback_iso (rigSection_snd ε t) M.isInvertible hK
  obtain ⟨e₄⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified M
  exact ⟨e₂ ≪≫ e₃ ≪≫ e₄⟩

end transportRigidify

theorem exists_transportHom (f : C' ⟶ C) (hf : f ≫ c = c')
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    ∃ θ : SchemeHomOver D.toBase D'.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a θ)).L ≅
          Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h).mul s x y) θ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h').mul s
            (NeronModelInfra.schemeHomOverComp x θ) (NeronModelInfra.schemeHomOverComp y θ)) ∧
      D.zeroSection ≫ θ.1 = D'.zeroSection := by
  obtain ⟨θ, hθ, -⟩ := RepresentsRelSubPic.existsUnique_hom_of_transform h' h (transportRigidify f hf ε ε')
    (fun t M M' e => transportRigidify.congr f hf M M' e) (fun ψ M => transportRigidify.nat f hf ψ M)
    (fun t M hM => transportRigidify.cut f hf M hM)
  have hmul := RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    (P := algEquivZeroGroupCut c' ε') (P' := algEquivZeroGroupCut c ε) h' h (transportRigidify f hf ε ε')
    (fun t M hM => transportRigidify.cut f hf M hM) (fun t M M' => transportRigidify.tensor f hf M M')
    (fun t => transportRigidify.unit f hf t) θ (fun t M hM => hθ t M hM)
  refine ⟨θ, fun t a => ?_, hmul.1, hmul.2⟩
  have hmem : (algEquivZeroCut c ε).P t (h.poincare.pullbackAlong a) :=
    (algEquivZeroCut c ε).pullback_mem _ _ a _ h.poincare_mem
  have ha : a = h.classify t _ hmem := h.classify_unique t _ hmem a ⟨Iso.refl _⟩
  have hcomp : NeronModelInfra.schemeHomOverComp a θ = postComp θ (h.classify t _ hmem) := by
    rw [← ha]; rfl
  rw [hcomp, hθ t _ hmem]
  exact h'.classify_spec t _ _

theorem transportHom_comp_eq_id (f : C' ⟶ C) (hf : f ≫ c = c') (f' : C ⟶ C') (hf' : f' ≫ c' = c)
    (hff' : f' ≫ f = 𝟙 C)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (θ : SchemeHomOver D.toBase D'.toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a θ)).L ≅
          Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L)))
    (θ' : SchemeHomOver D'.toBase D.toBase)
    (hθ' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D'.toBase),
        Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a θ')).L ≅
          Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
            ((Scheme.Modules.pullback (curveChange f' hf' t)).obj (h'.poincare.pullbackAlong a).L))) :
    θ.1 ≫ θ'.1 = 𝟙 D.P := by
  let one : SchemeHomOver D.toBase D.toBase := ⟨𝟙 _, Category.id_comp _⟩
  have key := h.ext_of_iso D.toBase
    (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp one θ) θ') one ?_
  · simpa [NeronModelInfra.schemeHomOverComp, one] using congrArg Subtype.val key
  obtain ⟨e₁⟩ := hθ' D.toBase (NeronModelInfra.schemeHomOverComp one θ)
  obtain ⟨e₂⟩ := hθ D.toBase one

  obtain ⟨e₃⟩ := transportRigidify.roundtrip (ε := ε) (ε' := ε') f hf f' hf' hff' (h.poincare.pullbackAlong one)
  exact ⟨e₁ ≪≫ Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso e₂) ≪≫ e₃⟩

section descent

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R'] {k' : Type u} [CommRing k']
  [Algebra R' k'] [Algebra R k']
  {X : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x}
  {D : RelativePic0Designation R x}
  {C' : Scheme.{u}} {c' : C' ⟶ Spec (CommRingCat.of R')} {e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) c'}
  {D' : RelativePic0Designation R' c'}
  {C'' : Scheme.{u}} {c'' : C'' ⟶ Spec (CommRingCat.of k')} {e'' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) c''}
  {D'' : RelativePic0Designation k' c''}

omit [Algebra R k'] in
theorem κ_inv_snd (cc : X ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ cc R' t').inv ≫ pullback.snd (baseChange R cc R') t' = pullback.snd cc (t' ≫ specMap R R') := by
  rw [Iso.inv_comp_eq, BaseChange.κ_hom_snd]

omit [Algebra R k'] in
theorem κ_inv_fst_fst (cc : X ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ cc R' t').inv ≫ pullback.fst (baseChange R cc R') t' ≫ pullback.fst cc (specMap R R') =
      pullback.fst cc (t' ≫ specMap R R') := by
  rw [Iso.inv_comp_eq, BaseChange.κ_hom_fst]

omit [Algebra R R'] in
theorem curveChange_fst {C₁ C₂ : Scheme.{u}} {c₁ : C₁ ⟶ Spec (CommRingCat.of R')} {c₂ : C₂ ⟶ Spec (CommRingCat.of R')}
    (f : C₂ ⟶ C₁) (hf : f ≫ c₁ = c₂) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    curveChange f hf t ≫ pullback.fst c₁ t = pullback.fst c₂ t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

theorem exists_pullbackRigidifyHom_descent
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (hs : RepresentsRelSubPic (baseChange R x k') (sectionBaseChange k' ε)
      (algEquivZeroCut (baseChange R x k') (sectionBaseChange k' ε)) (D.baseChange k'))
    (hPk : Nonempty (hs.poincare.L ≅ (BaseChange.ofR x ε k'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R k'), pullback.condition⟩)).L))
    (i' : C' ⟶ pullback x (specMap R R')) (hi' : i' ≫ baseChange R x R' = c')
    (h' : RepresentsRelSubPic c' e' (algEquivZeroCut c' e') D')
    (h'k : RepresentsRelSubPic (baseChange R' c' k') (sectionBaseChange k' e')
      (algEquivZeroCut (baseChange R' c' k') (sectionBaseChange k' e')) (D'.baseChange k'))
    (htie : Nonempty (h'k.poincare.L ≅ (BaseChange.ofR c' e' k'
      (h'.poincare.pullbackAlong ⟨pullback.fst D'.toBase (specMap R' k'), pullback.condition⟩)).L))
    (i'' : SchemeHomOver c'' (baseChange R x k'))
    (h'' : RepresentsRelSubPic c'' e'' (algEquivZeroCut c'' e'') D'')
    (f : pullback c' (specMap R' k') ⟶ C'') (hf : f ≫ c'' = baseChange R' c' k')
    (hfi : f ≫ i''.1 ≫ pullback.fst x (specMap R k') =
      pullback.fst c' (specMap R' k') ≫ i' ≫ pullback.fst x (specMap R R'))
    (θ : SchemeHomOver D''.toBase (D'.baseChange k').toBase)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k')) (a : SchemeHomOver t D''.toBase),
      Nonempty ((h'k.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a θ)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange R' c' k') t (sectionBaseChange k' e'))
          (pullback.snd (baseChange R' c' k') t)
          ((Scheme.Modules.pullback (curveChange f hf t)).obj (h''.poincare.pullbackAlong a).L)))
    (ν'' : SchemeHomOver (D.baseChange k').toBase D''.toBase)
    (hν'' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k')) (a : SchemeHomOver t (D.baseChange k').toBase),
      Nonempty ((h''.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν'')).L ≅
        Scheme.Modules.rigidify (rigSection c'' t e'') (pullback.snd c'' t)
          ((Scheme.Modules.pullback (curveChange i''.1 i''.2 t)).obj (hs.poincare.pullbackAlong a).L)))
    (π : pullback D.toBase (specMap R k') ⟶ pullback D.toBase (specMap R R'))
    (hπ₁ : π ≫ pullback.fst D.toBase (specMap R R') = pullback.fst D.toBase (specMap R k'))
    (hπ₂ : π ≫ pullback.snd D.toBase (specMap R R') = pullback.snd D.toBase (specMap R k') ≫ specMap R' k') :
    ∃ ν' : SchemeHomOver (D.baseChange R').toBase D'.toBase,
      ν''.1 ≫ θ.1 ≫ pullback.fst D'.toBase (specMap R' k') = π ≫ ν'.1 := by

  let t₁ : Limits.pullback D.toBase (specMap R R') ⟶ Spec (CommRingCat.of R') := (D.baseChange R').toBase
  let a₁ : SchemeHomOver (t₁ ≫ specMap R R') D.toBase := ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let t₀ : Limits.pullback D.toBase (specMap R k') ⟶ Spec (CommRingCat.of k') := (D.baseChange k').toBase
  let aK : SchemeHomOver (t₀ ≫ specMap R k') D.toBase := ⟨pullback.fst D.toBase (specMap R k'), pullback.condition⟩
  let t₀' : Limits.pullback D.toBase (specMap R k') ⟶ Spec (CommRingCat.of R') := t₀ ≫ specMap R' k'
  let πo : SchemeHomOver t₀' t₁ := ⟨π, hπ₂⟩

  let M₁ : RigidifiedLineBundle (baseChange R x R') (sectionBaseChange R' ε) t₁ :=
    BaseChange.ofR x ε R' (h.poincare.pullbackAlong a₁)
  have hM₁ : FibrewiseAlgEquivZero M₁ := by
    rw [← BaseChange.fibrewiseAlgEquivZero_toR_iff]
    exact FibrewiseAlgEquivZero.congr ⟨(BaseChange.toR_ofR_iso x ε R' _).symm⟩
      ((algEquivZeroCut x ε).pullback_mem _ _ a₁ _ h.poincare_mem)
  let N' : (Limits.pullback c' t₁).Modules := (Scheme.Modules.pullback (curveChange i' hi' t₁)).obj M₁.L
  have hN'inv : Scheme.Modules.IsInvertible N' := M₁.isInvertible.pullback _
  have hN' : ModAlgEquivZero c' t₁ N' := ModAlgEquivZero.curveChange i' hi' hM₁
  let B' : RigidifiedLineBundle c' e' t₁ := RigidifiedLineBundle.ofInvertible N' hN'inv
  have hB' : (algEquivZeroCut c' e').P t₁ B' := ModAlgEquivZero.ofInvertible hN'inv hN'
  let ν' : SchemeHomOver t₁ D'.toBase := h'.classify t₁ B' hB'
  have hν' : Nonempty ((h'.poincare.pullbackAlong ν').L ≅ B'.L) := h'.classify_spec t₁ B' hB'
  refine ⟨ν', ?_⟩

  let aF : SchemeHomOver ((D'.baseChange k').toBase ≫ specMap R' k') D'.toBase :=
    ⟨pullback.fst D'.toBase (specMap R' k'), pullback.condition⟩
  let ψ : SchemeHomOver t₀ (D'.baseChange k').toBase := NeronModelInfra.schemeHomOverComp ν'' θ
  let G₁ : SchemeHomOver t₀' D'.toBase := postComp aF (BaseChange.overR k' ψ)
  let G₂ : SchemeHomOver t₀' D'.toBase := postComp ν' πo
  suffices key : G₁ = G₂ by
    have := congrArg Subtype.val key
    simpa only [G₁, G₂, postComp, BaseChange.overR, ψ, NeronModelInfra.schemeHomOverComp, Category.assoc]
      using this
  refine h'.ext_of_iso t₀' G₁ G₂ ?_

  let σ₀ := rigSection c' t₀' e'
  let q₀ := pullback.snd c' t₀'
  let κ₀ := BaseChange.κ c' k' t₀
  let κX := BaseChange.κ x k' t₀
  let κX' := BaseChange.κ x R' t₁
  let ΦL : Limits.pullback c' t₀' ⟶ Limits.pullback x D.toBase :=
    κ₀.inv ≫ curveChange f hf t₀ ≫ curveChange i''.1 i''.2 t₀ ≫ κX.hom ≫ baseChangeSnd x aK
  let ΦR : Limits.pullback c' t₀' ⟶ Limits.pullback x D.toBase :=
    baseChangeSnd c' πo ≫ curveChange i' hi' t₁ ≫ κX'.hom ≫ baseChangeSnd x a₁
  have hΦ : ΦL = ΦR := by
    apply pullback.hom_ext
    ·
      have eL : ΦL ≫ pullback.fst x D.toBase = pullback.fst c' t₀' ≫ i' ≫ pullback.fst x (specMap R R') := by
        simp only [ΦL, Category.assoc]
        rw [BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst, ← Category.assoc (curveChange i''.1 i''.2 t₀),
          curveChange_fst, Category.assoc, ← Category.assoc (curveChange f hf t₀), curveChange_fst, Category.assoc,
          hfi, ← Category.assoc, ← Category.assoc, Category.assoc κ₀.inv, κ_inv_fst_fst]
      have eR : ΦR ≫ pullback.fst x D.toBase = pullback.fst c' t₀' ≫ i' ≫ pullback.fst x (specMap R R') := by
        simp only [ΦR, Category.assoc]
        rw [BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst, ← Category.assoc (curveChange i' hi' t₁),
          curveChange_fst, Category.assoc, ← Category.assoc, BaseChange.baseChangeSnd_fst']
      rw [eL, eR]
    ·
      have eL : ΦL ≫ pullback.snd x D.toBase = pullback.snd c' t₀' ≫ pullback.fst D.toBase (specMap R k') := by
        simp only [ΦL, Category.assoc]
        rw [BaseChange.baseChangeSnd_snd', ← Category.assoc κX.hom, BaseChange.κ_hom_snd,
          ← Category.assoc (curveChange i''.1 i''.2 t₀), curveChange_snd, ← Category.assoc (curveChange f hf t₀),
          curveChange_snd, ← Category.assoc, κ_inv_snd]
      have eR : ΦR ≫ pullback.snd x D.toBase = pullback.snd c' t₀' ≫ pullback.fst D.toBase (specMap R k') := by
        simp only [ΦR, Category.assoc]
        rw [BaseChange.baseChangeSnd_snd', ← Category.assoc κX'.hom, BaseChange.κ_hom_snd,
          ← Category.assoc (curveChange i' hi' t₁), curveChange_snd, ← Category.assoc,
          BaseChange.baseChangeSnd_snd', Category.assoc]
        change pullback.snd c' t₀' ≫ π ≫ pullback.fst D.toBase (specMap R R') = _
        rw [hπ₁]
      rw [eL, eR]

  have hR : Nonempty ((h'.poincare.pullbackAlong G₂).L ≅
      Scheme.Modules.rigidify σ₀ q₀ ((Scheme.Modules.pullback ΦR).obj h.poincare.L)) := by
    obtain ⟨e₁⟩ := hν'
    obtain ⟨e₂⟩ := Scheme.Modules.nonempty_pullback_rigidify_iso (σ := rigSection c' t₁ e') (q := pullback.snd c' t₁)
      (σ' := σ₀) (q' := q₀) (baseChangeSnd c' πo) π (rigSection_baseChangeSnd c' e' πo)
      (BaseChange.baseChangeSnd_snd' R' c' πo) hN'inv
    refine ⟨(h'.poincare.pullbackAlongPullbackAlongIso' ν' πo).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c' πo)).mapIso e₁ ≪≫ e₂ ≪≫ Scheme.Modules.rigidifyMapIso _ _ ?_⟩

    exact (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso
        ((Scheme.Modules.pullbackComp _ _).app _) ≪≫ (Scheme.Modules.pullbackComp _ _).app _) ≪≫
      (Scheme.Modules.pullbackComp _ _).app _

  have hL : Nonempty ((h'.poincare.pullbackAlong G₁).L ≅
      Scheme.Modules.rigidify σ₀ q₀ ((Scheme.Modules.pullback ΦL).obj h.poincare.L)) := by

    have eA : Nonempty ((h'.poincare.pullbackAlong G₁).L ≅
        (Scheme.Modules.pullback κ₀.inv).obj (h'k.poincare.pullbackAlong ψ).L) := by
      refine ⟨(h'.poincare.pullbackAlongPullbackAlongIso' aF (BaseChange.overR k' ψ)).symm ≪≫
        (Scheme.Modules.pullback (baseChangeSnd c' (BaseChange.overR k' ψ))).mapIso
          ((BaseChange.toR_ofR_iso c' e' k' _).symm ≪≫
            (Scheme.Modules.pullback (BaseChange.κ c' k' _).inv).mapIso htie.some.symm) ≪≫
        BaseChange.toR_pullbackAlong_iso c' e' k' ψ h'k.poincare⟩

    obtain ⟨eθ⟩ := hθ t₀ ν''
    let one₀ : SchemeHomOver t₀ (D.baseChange k').toBase := ⟨𝟙 _, Category.id_comp _⟩
    obtain ⟨eν⟩ := hν'' t₀ one₀
    have hone : NeronModelInfra.schemeHomOverComp one₀ ν'' = ν'' := Subtype.ext (Category.id_comp _)
    rw [hone] at eν
    have eone : (hs.poincare.pullbackAlong one₀).L ≅ hs.poincare.L :=
      (Scheme.Modules.pullbackCongr (baseChangeSnd_id _ t₀)).app _ ≪≫ (Scheme.Modules.pullbackId _).app _

    let X₁ : (Limits.pullback c'' t₀).Modules :=
      (Scheme.Modules.pullback (curveChange i''.1 i''.2 t₀)).obj (hs.poincare.pullbackAlong one₀).L
    have hX₁ : Scheme.Modules.IsInvertible X₁ := (hs.poincare.pullbackAlong one₀).isInvertible.pullback _
    let K₁ := rigCorrection e'' t₀ X₁
    have hK₁ : Scheme.Modules.IsInvertible K₁ := ((hX₁.pullback _).dual).1

    let eB : (Scheme.Modules.pullback (curveChange f hf t₀)).obj (Scheme.Modules.rigidify (rigSection c'' t₀ e'')
        (pullback.snd c'' t₀) X₁) ≅
        (Scheme.Modules.pullback (curveChange f hf t₀)).obj X₁ ⊗
          (Scheme.Modules.pullback (pullback.snd (baseChange R' c' k') t₀)).obj K₁ :=
      Scheme.Modules.pullbackTensorPullbackIso _ (curveChange_snd f hf t₀) _ _
    obtain ⟨eC⟩ := Scheme.Modules.nonempty_rigidify_tensor_pullback_iso
      (rigSection_snd (sectionBaseChange k' e') t₀) (hX₁.pullback (curveChange f hf t₀)) hK₁

    obtain ⟨eD⟩ := Scheme.Modules.nonempty_pullback_rigidify_iso
      (σ := rigSection (baseChange R' c' k') t₀ (sectionBaseChange k' e')) (q := pullback.snd (baseChange R' c' k') t₀)
      (σ' := σ₀) (q' := q₀) κ₀.inv (𝟙 _)
      (by rw [Category.id_comp]; exact BaseChange.rigSection_κ_inv c' e' k' t₀)
      (by rw [Category.comp_id]; exact κ_inv_snd c' t₀) (hX₁.pullback (curveChange f hf t₀))
    obtain ⟨eA⟩ := eA
    refine ⟨eA ≪≫ (Scheme.Modules.pullback κ₀.inv).mapIso (eθ ≪≫ Scheme.Modules.rigidifyMapIso _ _
        ((Scheme.Modules.pullback _).mapIso eν ≪≫ eB) ≪≫ eC) ≪≫ eD ≪≫ Scheme.Modules.rigidifyMapIso _ _ ?_⟩

    refine (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso
        ((Scheme.Modules.pullback _).mapIso (eone ≪≫ hPk.some ≪≫ (Scheme.Modules.pullbackComp _ _).app _) ≪≫
          (Scheme.Modules.pullbackComp _ _).app _) ≪≫
        (Scheme.Modules.pullbackComp _ _).app _) ≪≫
      (Scheme.Modules.pullbackComp _ _).app _
  exact ⟨hL.some ≪≫ Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullbackCongr hΦ).app _) ≪≫ hR.some.symm⟩

end descent

end AlgebraicGeometry.RelPicard

end

open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))

    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [Algebra A (ZMod p)] [Algebra (ZMod p) k] [IsScalarTower A (ZMod p) k]
    (C₁ₚ C₂ₚ : Scheme.{0}) (c₁ₚ : C₁ₚ ⟶ Spec (CommRingCat.of (ZMod p))) (c₂ₚ : C₂ₚ ⟶ Spec (CommRingCat.of (ZMod p)))
    (i₁ₚ : C₁ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
    (i₂ₚ : C₂ₚ ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)))
    (g₁ : C₁ ⟶ C₁ₚ) (g₂ : C₂ ⟶ C₂ₚ)
    [IsProper c₁ₚ] [SmoothOfRelativeDimension 1 c₁ₚ] [GeometricallyIntegral c₁ₚ]
    [IsProper c₂ₚ] [SmoothOfRelativeDimension 1 c₂ₚ] [GeometricallyIntegral c₂ₚ]
    (ε₁ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₁ₚ) (ε₂ₚ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ZMod p)))) c₂ₚ)
    (hg₁ : IsPullback g₁ c₁ c₁ₚ (specMap (ZMod p) k)) (hg₂ : IsPullback g₂ c₂ c₂ₚ (specMap (ZMod p) k))
    (hi₁ₚ : i₁ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₁ₚ) (hi₂ₚ : i₂ₚ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = c₂ₚ)
    (hgi₁ : g₁ ≫ i₁ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hgi₂ : g₂ ≫ i₂ₚ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) = i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (D₁ₚ : RelativePic0Designation (ZMod p) c₁ₚ) (D₂ₚ : RelativePic0Designation (ZMod p) c₂ₚ)
    (hrep₁ₚ : RepresentsRelSubPic c₁ₚ ε₁ₚ (algEquivZeroCut c₁ₚ ε₁ₚ) D₁ₚ)
    (hrep₂ₚ : RepresentsRelSubPic c₂ₚ ε₂ₚ (algEquivZeroCut c₂ₚ ε₂ₚ) D₂ₚ)
    (hrep₁ₚk : RepresentsRelSubPic (baseChange (ZMod p) c₁ₚ k) (sectionBaseChange k ε₁ₚ)
      (algEquivZeroCut (baseChange (ZMod p) c₁ₚ k) (sectionBaseChange k ε₁ₚ)) (D₁ₚ.baseChange k))
    (hrep₂ₚk : RepresentsRelSubPic (baseChange (ZMod p) c₂ₚ k) (sectionBaseChange k ε₂ₚ)
      (algEquivZeroCut (baseChange (ZMod p) c₂ₚ k) (sectionBaseChange k ε₂ₚ)) (D₂ₚ.baseChange k))
    (htie₁ : Nonempty (hrep₁ₚk.poincare.L ≅ (BaseChange.ofR c₁ₚ ε₁ₚ k
        (hrep₁ₚ.poincare.pullbackAlong ⟨pullback.fst D₁ₚ.toBase (specMap (ZMod p) k), pullback.condition⟩)).L))
    (htie₂ : Nonempty (hrep₂ₚk.poincare.L ≅ (BaseChange.ofR c₂ₚ ε₂ₚ k
        (hrep₂ₚ.poincare.pullbackAlong ⟨pullback.fst D₂ₚ.toBase (specMap (ZMod p) k), pullback.condition⟩)).L)) :
    ∃ (θ₁ : SchemeHomOver D₁.toBase (D₁ₚ.baseChange k).toBase) (θ₂ : SchemeHomOver D₂.toBase (D₂ₚ.baseChange k).toBase)
      (πₚ : pullback D.toBase (specMap A k) ⟶ pullback D.toBase (specMap A (ZMod p)))
      (ν₁ₚ : SchemeHomOver (D.baseChange (ZMod p)).toBase D₁ₚ.toBase) (ν₂ₚ : SchemeHomOver (D.baseChange (ZMod p)).toBase D₂ₚ.toBase),
      IsIso θ₁.1 ∧ IsIso θ₂.1 ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s D₁.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).mul s x y) θ₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁ₚk).mul s (NeronModelInfra.schemeHomOverComp x θ₁) (NeronModelInfra.schemeHomOverComp y θ₁)) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s D₂.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).mul s x y) θ₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂ₚk).mul s (NeronModelInfra.schemeHomOverComp x θ₂) (NeronModelInfra.schemeHomOverComp y θ₂)) ∧
      πₚ ≫ pullback.fst D.toBase (specMap A (ZMod p)) = pullback.fst D.toBase (specMap A k) ∧
      πₚ ≫ pullback.snd D.toBase (specMap A (ZMod p)) = pullback.snd D.toBase (specMap A k) ≫ specMap (ZMod p) k ∧
      (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some).1 ≫ θ₁.1 ≫ pullback.fst D₁ₚ.toBase (specMap (ZMod p) k) = πₚ ≫ ν₁ₚ.1 ∧
      ν₂.1 ≫ θ₂.1 ≫ pullback.fst D₂ₚ.toBase (specMap (ZMod p) k) = πₚ ≫ ν₂ₚ.1 := by

  have hspec : specMap A k = specMap (ZMod p) k ≫ specMap A (ZMod p) := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let πₚ : pullback D.toBase (specMap A k) ⟶ pullback D.toBase (specMap A (ZMod p)) :=
    pullback.lift (pullback.fst D.toBase (specMap A k)) (pullback.snd D.toBase (specMap A k) ≫ specMap (ZMod p) k)
      (by rw [pullback.condition, Category.assoc, ← hspec])
  have hπ₁ : πₚ ≫ pullback.fst D.toBase (specMap A (ZMod p)) = pullback.fst D.toBase (specMap A k) :=
    pullback.lift_fst _ _ _
  have hπ₂ : πₚ ≫ pullback.snd D.toBase (specMap A (ZMod p)) =
      pullback.snd D.toBase (specMap A k) ≫ specMap (ZMod p) k :=
    pullback.lift_snd _ _ _

  let f₁ : pullback c₁ₚ (specMap (ZMod p) k) ⟶ C₁ := hg₁.isoPullback.inv
  have hf₁ : f₁ ≫ c₁ = baseChange (ZMod p) c₁ₚ k := hg₁.isoPullback_inv_snd
  have hf₁' : hg₁.isoPullback.hom ≫ baseChange (ZMod p) c₁ₚ k = c₁ := hg₁.isoPullback_hom_snd
  let f₂ : pullback c₂ₚ (specMap (ZMod p) k) ⟶ C₂ := hg₂.isoPullback.inv
  have hf₂ : f₂ ≫ c₂ = baseChange (ZMod p) c₂ₚ k := hg₂.isoPullback_inv_snd
  have hf₂' : hg₂.isoPullback.hom ≫ baseChange (ZMod p) c₂ₚ k = c₂ := hg₂.isoPullback_hom_snd
  obtain ⟨θ₁, hθ₁, hθ₁mul, -⟩ := AlgebraicGeometry.RelPicard.exists_transportHom
    (ε := ε₁) (ε' := sectionBaseChange k ε₁ₚ) f₁ hf₁ hrep₁.some hrep₁ₚk
  obtain ⟨θ₁', hθ₁', -, -⟩ := AlgebraicGeometry.RelPicard.exists_transportHom
    (ε := sectionBaseChange k ε₁ₚ) (ε' := ε₁) hg₁.isoPullback.hom hf₁' hrep₁ₚk hrep₁.some
  obtain ⟨θ₂, hθ₂, hθ₂mul, -⟩ := AlgebraicGeometry.RelPicard.exists_transportHom
    (ε := ε₂) (ε' := sectionBaseChange k ε₂ₚ) f₂ hf₂ hrep₂.some hrep₂ₚk
  obtain ⟨θ₂', hθ₂', -, -⟩ := AlgebraicGeometry.RelPicard.exists_transportHom
    (ε := sectionBaseChange k ε₂ₚ) (ε' := ε₂) hg₂.isoPullback.hom hf₂' hrep₂ₚk hrep₂.some
  have iso₁ : IsIso θ₁.1 :=
    ⟨⟨θ₁'.1,
      AlgebraicGeometry.RelPicard.transportHom_comp_eq_id f₁ hf₁ hg₁.isoPullback.hom hf₁' hg₁.isoPullback.hom_inv_id
        hrep₁.some hrep₁ₚk θ₁ hθ₁ θ₁' hθ₁',
      AlgebraicGeometry.RelPicard.transportHom_comp_eq_id hg₁.isoPullback.hom hf₁' f₁ hf₁ hg₁.isoPullback.inv_hom_id
        hrep₁ₚk hrep₁.some θ₁' hθ₁' θ₁ hθ₁⟩⟩
  have iso₂ : IsIso θ₂.1 :=
    ⟨⟨θ₂'.1,
      AlgebraicGeometry.RelPicard.transportHom_comp_eq_id f₂ hf₂ hg₂.isoPullback.hom hf₂' hg₂.isoPullback.hom_inv_id
        hrep₂.some hrep₂ₚk θ₂ hθ₂ θ₂' hθ₂',
      AlgebraicGeometry.RelPicard.transportHom_comp_eq_id hg₂.isoPullback.hom hf₂' f₂ hf₂ hg₂.isoPullback.inv_hom_id
        hrep₂ₚk hrep₂.some θ₂' hθ₂' θ₂ hθ₂⟩⟩

  have hfi₁ : f₁ ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst c₁ₚ (specMap (ZMod p) k) ≫ i₁ₚ ≫
        pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) := by
    rw [← hgi₁, ← Category.assoc f₁ g₁, hg₁.isoPullback_inv_fst]
  have hfi₂ : f₂ ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst c₂ₚ (specMap (ZMod p) k) ≫ i₂ₚ ≫
        pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) := by
    rw [← hgi₂, ← Category.assoc f₂ g₂, hg₂.isoPullback_inv_fst]

  have hν₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a
        (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some))).L ≅
        Scheme.Modules.rigidify (rigSection c₁ t ε₁) (pullback.snd c₁ t)
          ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj (hreps.poincare.pullbackAlong a).L)) := by
    intro T t a
    have hmem : (algEquivZeroCut _ _).P t (hreps.poincare.pullbackAlong a) :=
      (algEquivZeroCut _ _).pullback_mem _ _ a _ hreps.poincare_mem
    have ha : a = hreps.classify t _ hmem := hreps.classify_unique t _ hmem a ⟨Iso.refl _⟩
    have hcomp : NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (hreps.classify t _ hmem) := by
      rw [← ha]; rfl
    rw [hcomp, RepresentsRelSubPic.postComp_pullbackHom_classify]
    obtain ⟨e⟩ := hrep₁.some.classify_spec t ((hreps.poincare.pullbackAlong a).pullbackCurve i₁.1 i₁.2 hε₁)
      (FibrewiseAlgEquivZero.pullbackCurve i₁.1 i₁.2 hε₁ hmem)
    exact ⟨e ≪≫ (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified _).some.symm⟩
  obtain ⟨ν₁ₚ, h₇⟩ := AlgebraicGeometry.RelPicard.exists_pullbackRigidifyHom_descent hrep.some hreps hPk i₁ₚ hi₁ₚ
    hrep₁ₚ hrep₁ₚk htie₁ i₁ hrep₁.some f₁ hf₁ hfi₁ θ₁ hθ₁
    (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) hν₁ πₚ hπ₁ hπ₂
  obtain ⟨ν₂ₚ, h₈⟩ := AlgebraicGeometry.RelPicard.exists_pullbackRigidifyHom_descent hrep.some hreps hPk i₂ₚ hi₂ₚ
    hrep₂ₚ hrep₂ₚk htie₂ i₂ hrep₂.some f₂ hf₂ hfi₂ θ₂ hθ₂ ν₂ hν₂ πₚ hπ₁ hπ₂
  exact ⟨θ₁, θ₂, πₚ, ν₁ₚ, ν₂ₚ, iso₁, iso₂, hθ₁mul, hθ₂mul, hπ₁, hπ₂, h₇, h₈⟩

end S_ModularCurve_XOneP_exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_iso_pic0_baseChange_and_descent_projections_specialFibre_twoChartModel_x1_mul (solution)
