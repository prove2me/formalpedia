-- Prove2me | solution 1 for ModularCurve.XOneP.existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/380830e3-f3c7-5cb6-8815-df37aeaf3590

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
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve"

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper morphismRestrict_ι Scheme.Modules.pullback GeometricallyIntegral Spec Spec.map Scheme Smooth IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules Scheme.hom_ext_of_forall Scheme.presieve₀_mem_precoverage_iff Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RepresentsRelSubPic Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut curveChange curveChange_snd RepresentsRelSubPic.pullbackHom RigidifiedLineBundle.tensor_congr SubPicGroupCondition RepresentsRelSubPic.relativeGroupLaw algEquivZeroGroupCut rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.ofInvertible_L_eq_tensor RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform"
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

namespace RepresentsRelSubPic
p2m_export "AlgebraicGeometry.RelPicard.RepresentsRelSubPic" "classify classify_spec classify_unique ext_of_iso poincare zero mk pullbackHom grpObj relativeGroupLaw homEquiv_mul comp_mul_eq_mul_comp_of_transform"
p2m_open "AlgebraicGeometry.RelPicard.RepresentsRelSubPic"

section MulIso

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}

theorem nonempty_poincare_pullbackAlong_mul_iso (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t x y)).L ≅
      ((h.poincare.pullbackAlong x).tensor (h.poincare.pullbackAlong y)).L) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op (Over.mk t))
  have hmul := h.homEquiv_mul (Over.mk t) (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  have hval := congrArg Subtype.val hmul

  change Quotient.mk _ (h.poincare.pullbackAlong ⟨(schemeHomOverToOverHom x * schemeHomOverToOverHom y).left, _⟩) =
    Quotient.map₂ (fun L M => L.tensor M) (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM)
      (Quotient.mk _ (h.poincare.pullbackAlong ⟨(schemeHomOverToOverHom x).left, _⟩))
      (Quotient.mk _ (h.poincare.pullbackAlong ⟨(schemeHomOverToOverHom y).left, _⟩)) at hval
  exact Quotient.exact hval

end MulIso

section Hom

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
  (h : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D)
  (h' : RepresentsRelSubPic c' ε' (algEquivZeroGroupCut c' ε').toSubPicCondition D')

def poincarePullbackAlongPostCompPullbackHomIso {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (z : SchemeHomOver t D.toBase) :
    (h'.poincare.pullbackAlong (postComp (pullbackHom f hf hε h h') z)).L ≅
      ((h.poincare.pullbackAlong z).pullbackCurve f hf hε).L :=
  (h'.poincare.pullbackAlongPullbackAlongIso' _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h'.classify_spec D.toBase _ _).some ≪≫
    (h.poincare.pullbackCurvePullbackAlongIso f hf hε _)

theorem postComp_pullbackHom_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t D.toBase) :
    postComp (pullbackHom f hf hε h h') (h.relativeGroupLaw.mul t x y) =
      h'.relativeGroupLaw.mul t (postComp (pullbackHom f hf hε h h') x) (postComp (pullbackHom f hf hε h h') y) := by
  apply h'.ext_of_iso t
  obtain ⟨eD⟩ := nonempty_poincare_pullbackAlong_mul_iso h t x y
  obtain ⟨eD'⟩ := nonempty_poincare_pullbackAlong_mul_iso h' t
    (postComp (pullbackHom f hf hε h h') x) (postComp (pullbackHom f hf hε h h') y)
  refine ⟨poincarePullbackAlongPostCompPullbackHomIso f hf hε h h' _ ≪≫
    (Scheme.Modules.pullback _).mapIso eD ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    ((poincarePullbackAlongPostCompPullbackHomIso f hf hε h h' x).symm ⊗ᵢ
      (poincarePullbackAlongPostCompPullbackHomIso f hf hε h h' y).symm) ≪≫ eD'.symm⟩

end Hom

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper morphismRestrict_ι Scheme.Modules.pullback GeometricallyIntegral Spec Spec.map Scheme Smooth IsClosedImmersion IsReduced IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules Scheme.hom_ext_of_forall Scheme.presieve₀_mem_precoverage_iff Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso RelPicard.RepresentsRelSubPic Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut curveChange curveChange_snd RepresentsRelSubPic.pullbackHom RigidifiedLineBundle.tensor_congr SubPicGroupCondition RepresentsRelSubPic.relativeGroupLaw algEquivZeroGroupCut rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.ofInvertible_L_eq_tensor RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform"
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

namespace HomNu2Aux

theorem nonempty_pullback_fst_ofInvertible_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L : (pullback c t).Modules)
    (hL : Scheme.Modules.IsInvertible L) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj L) := by
  rw [RigidifiedLineBundle.ofInvertible_L_eq_tensor]

  have hD : Scheme.Modules.IsInvertible (rigCorrection ε t L) := ((hL.pullback _).dual).1
  obtain ⟨u⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hD.pullback s)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := pullback.snd c t) (g := s))).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c')

abbrev psi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (Limits.pullback c' t).Modules :=
  (Scheme.Modules.pullback (curveChange f hf t)).obj M.L

theorem psi_isInvertible {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible (psi f hf t M) :=
  M.isInvertible.pullback _

def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  RigidifiedLineBundle.ofInvertible (ε := ε') (psi f hf t M) (psi_isInvertible f hf t M)

include hf in

theorem isAlgEquivZero_psi {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M : RigidifiedLineBundle c ε t} (hM : FibrewiseAlgEquivZero M)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c' t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c' t) s)).obj (psi f hf t M)) := by
  let e : Limits.pullback (pullback.snd c' t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange f hf t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt c' t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ curveChange f hf t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

include hf in
theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi (ε' := ε') f hf t M) := by
  intro k _ _ s
  obtain ⟨e⟩ := nonempty_pullback_fst_ofInvertible_iso (ε := ε') (psi f hf t M) (psi_isInvertible f hf t M) s
  exact (isAlgEquivZero_psi f hf hM k s).of_iso e.symm

theorem htensor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t) :
    Nonempty ((Phi (ε' := ε') f hf t (M.tensor M')).L ≅
      ((Phi (ε' := ε') f hf t M).tensor (Phi (ε' := ε') f hf t M')).L) := by
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    (psi_isInvertible f hf t (M.tensor M')) ((psi_isInvertible f hf t M).tensor (psi_isInvertible f hf t M'))
    (Scheme.Modules.pullbackTensorObjIso _ _ _)
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε')
    (psi_isInvertible f hf t M) (psi_isInvertible f hf t M')
  exact ⟨e1 ≪≫ e2⟩

theorem hunit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Phi (ε' := ε') f hf t (RigidifiedLineBundle.unit (c := c) (ε := ε) t)).L ≅
      (RigidifiedLineBundle.unit (c := c') (ε := ε') t).L) := by
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε')
    (psi_isInvertible f hf t (RigidifiedLineBundle.unit t))
    (RigidifiedLineBundle.unit (c := c') (ε := ε') t).isInvertible (Scheme.Modules.pullbackUnitIso _)
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c') (ε := ε') t)
  exact ⟨e1 ≪≫ e2⟩

end HomNu2Aux

namespace RepresentsRelSubPic
p2m_export "AlgebraicGeometry.RelPicard.RepresentsRelSubPic" "classify classify_spec classify_unique ext_of_iso poincare zero mk pullbackHom grpObj relativeGroupLaw homEquiv_mul comp_mul_eq_mul_comp_of_transform"
p2m_open "AlgebraicGeometry.RelPicard.RepresentsRelSubPic"

open HomNu2Aux

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c')
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
  (h : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D)
  (h' : RepresentsRelSubPic c' ε' (algEquivZeroGroupCut c' ε').toSubPicCondition D')
  (g : SchemeHomOver D.toBase D'.toBase)
  (hg : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
    Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a g)).L ≅
      Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L)))

include hg in

theorem comp_mul_eq_mul_comp_of_classifies_rigidify_pullback_curveChange :
    (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp (h.relativeGroupLaw.mul s x y) g =
        h'.relativeGroupLaw.mul s (NeronModelInfra.schemeHomOverComp x g)
          (NeronModelInfra.schemeHomOverComp y g)) ∧
    D.zeroSection ≫ g.1 = D'.zeroSection := by
  have hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
      (hM : (algEquivZeroGroupCut c ε).toSubPicCondition.P t M),
      postComp g (h.classify t M hM) =
        h'.classify t (Phi (ε' := ε') f hf t M) (hcut (ε' := ε') f hf t M hM) := by
    intro T t M hM
    apply h'.classify_unique
    obtain ⟨e1⟩ := hg t (h.classify t M hM)
    obtain ⟨e2⟩ := h.classify_spec t M hM
    exact ⟨e1 ≪≫ Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso e2)⟩
  exact RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    (P := algEquivZeroGroupCut c' ε') (P' := algEquivZeroGroupCut c ε) h' h (Phi (ε' := ε') f hf)
    (fun t M hM => hcut (ε' := ε') f hf t M hM) (fun t M M' => htensor (ε' := ε') f hf t M M')
    (fun t => hunit (ε' := ε') f hf t) g (fun t M hM => hφ t M hM)

include hg in

theorem postComp_mul_of_classifies_rigidify_pullback_curveChange
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase) :
    postComp g (h.relativeGroupLaw.mul s x y) = h'.relativeGroupLaw.mul s (postComp g x) (postComp g y) :=
  (comp_mul_eq_mul_comp_of_classifies_rigidify_pullback_curveChange f hf h h' g hg).1 s x y

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul.AlgebraicGeometry.RelPicard"

namespace K6Core

variable {k : Type u} [CommRing k]
variable {Ds D₁ D₂ TT Y : Scheme.{u}}
variable {fs : Ds ⟶ Spec (CommRingCat.of k)} {f₁ : D₁ ⟶ Spec (CommRingCat.of k)} {f₂ : D₂ ⟶ Spec (CommRingCat.of k)}
variable {tT : TT ⟶ Spec (CommRingCat.of k)} {gY : Y ⟶ Spec (CommRingCat.of k)}
variable (Ls : RelativeGroupLaw k fs) (L₁ : RelativeGroupLaw k f₁) (L₂ : RelativeGroupLaw k f₂)
  (LY : RelativeGroupLaw k gY)
variable (ν₁ : SchemeHomOver fs f₁) (ν₂ : SchemeHomOver fs f₂) (jT : SchemeHomOver tT fs) (ψ : SchemeHomOver fs gY)

structure Hyp : Prop where
  hν₁ : ∀ {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s fs),
    postComp ν₁ (Ls.mul s x y) = L₁.mul s (postComp ν₁ x) (postComp ν₁ y)
  hν₂ : ∀ {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s fs),
    postComp ν₂ (Ls.mul s x y) = L₂.mul s (postComp ν₂ x) (postComp ν₂ y)
  hψ : ∀ {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s fs),
    NeronModelInfra.schemeHomOverComp (Ls.mul s x y) ψ =
      LY.mul s (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)
  hker : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t fs),
    (postComp ν₁ x = L₁.one t ∧ postComp ν₂ x = L₂.one t) → ∃ y : SchemeHomOver t tT, NeronModelInfra.schemeHomOverComp y jT = x
  hepi : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (x₁ : SchemeHomOver t f₁) (x₂ : SchemeHomOver t f₂)
    (z : T'), ∃ (U : T'.Opens) (_ : z ∈ U) (x : SchemeHomOver (U.ι ≫ t) fs),
      (postComp ν₁ x).1 = U.ι ≫ x₁.1 ∧ (postComp ν₂ x).1 = U.ι ≫ x₂.1
  hψT : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (y : SchemeHomOver t tT),
    NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp y jT) ψ = LY.one t

variable {Ls L₁ L₂ LY ν₁ ν₂ jT ψ}

theorem comp_ψ_eq_of_proj_eq (H : Hyp Ls L₁ L₂ LY ν₁ ν₂ jT ψ) {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of k))
    (a b : SchemeHomOver w fs) (h1 : postComp ν₁ a = postComp ν₁ b) (h2 : postComp ν₂ a = postComp ν₂ b) :
    NeronModelInfra.schemeHomOverComp a ψ = NeronModelInfra.schemeHomOverComp b ψ := by
  letI := Ls.pointGroup w
  letI := L₁.pointGroup w
  letI := L₂.pointGroup w
  letI := LY.pointGroup w
  let φ₁ : SchemeHomOver w fs →* SchemeHomOver w f₁ := MonoidHom.mk' (fun x => postComp ν₁ x) (H.hν₁ w)
  let φ₂ : SchemeHomOver w fs →* SchemeHomOver w f₂ := MonoidHom.mk' (fun x => postComp ν₂ x) (H.hν₂ w)
  let φY : SchemeHomOver w fs →* SchemeHomOver w gY :=
    MonoidHom.mk' (fun x => NeronModelInfra.schemeHomOverComp x ψ) (H.hψ w)

  have hd1 : postComp ν₁ (a * b⁻¹) = L₁.one w := by
    change φ₁ (a * b⁻¹) = 1
    rw [map_mul, map_inv]
    change postComp ν₁ a * (postComp ν₁ b)⁻¹ = 1
    rw [h1, mul_inv_cancel]
  have hd2 : postComp ν₂ (a * b⁻¹) = L₂.one w := by
    change φ₂ (a * b⁻¹) = 1
    rw [map_mul, map_inv]
    change postComp ν₂ a * (postComp ν₂ b)⁻¹ = 1
    rw [h2, mul_inv_cancel]
  obtain ⟨y, hy⟩ := H.hker w (a * b⁻¹) ⟨hd1, hd2⟩
  have hψd : NeronModelInfra.schemeHomOverComp (a * b⁻¹) ψ = LY.one w := by
    rw [← hy]; exact H.hψT w y
  have hab : a = (a * b⁻¹) * b := by rw [inv_mul_cancel_right]
  calc NeronModelInfra.schemeHomOverComp a ψ
      = φY a := rfl
    _ = φY (a * b⁻¹) * φY b := by rw [hab, map_mul, ← hab]
    _ = NeronModelInfra.schemeHomOverComp b ψ := by
        change LY.mul w (NeronModelInfra.schemeHomOverComp (a * b⁻¹) ψ) _ = _
        rw [hψd, LY.one_mul]
        rfl

theorem postComp_restrict {A B : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} {fB : B ⟶ Spec (CommRingCat.of k)}
    (g : SchemeHomOver fA fB) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (r : T' ⟶ T) (hr : r ≫ t = t') (x : SchemeHomOver t fA) :
    postComp g (GoodReductionJacobian.schemeHomOverComp r hr x) = GoodReductionJacobian.schemeHomOverComp r hr (postComp g x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem comp_restrict {A B : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} {fB : B ⟶ Spec (CommRingCat.of k)}
    (g : SchemeHomOver fA fB) {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (r : T' ⟶ T) (hr : r ≫ t = t') (x : SchemeHomOver t fA) :
    NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp r hr x) g =
      GoodReductionJacobian.schemeHomOverComp r hr (NeronModelInfra.schemeHomOverComp x g) :=
  Subtype.ext (Category.assoc _ _ _)

theorem existsUnique_factor (H : Hyp Ls L₁ L₂ LY ν₁ ν₂ jT ψ) :
    ∃! ψbar : SchemeHomOver (prodStr f₁ f₂) gY,
      (∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t fs),
        NeronModelInfra.schemeHomOverComp x ψ =
          NeronModelInfra.schemeHomOverComp (prodPairPt (postComp ν₁ x) (postComp ν₂ x)) ψbar) ∧
      (∀ {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver s (prodStr f₁ f₂)),
        NeronModelInfra.schemeHomOverComp ((L₁.prod L₂).mul s a b) ψbar =
          LY.mul s (NeronModelInfra.schemeHomOverComp a ψbar) (NeronModelInfra.schemeHomOverComp b ψbar)) := by
  classical

  set P : Scheme.{u} := pullback f₁ f₂ with hP
  set t₀ : P ⟶ Spec (CommRingCat.of k) := prodStr f₁ f₂ with ht₀
  let idP : SchemeHomOver t₀ (prodStr f₁ f₂) := ⟨𝟙 P, Category.id_comp _⟩
  let u₁ : SchemeHomOver t₀ f₁ := prodFstPt idP
  let u₂ : SchemeHomOver t₀ f₂ := prodSndPt idP
  have hu₁ : u₁.1 = pullback.fst f₁ f₂ := Category.id_comp _
  have hu₂ : u₂.1 = pullback.snd f₁ f₂ := Category.id_comp _

  choose U hU xU hxU1 hxU2 using fun z : P => H.hepi t₀ u₁ u₂ z

  let 𝒰 : P.OpenCover :=
    { I₀ := P, X := fun z => (U z : Scheme.{u}), f := fun z => (U z).ι,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun z => ⟨z, by simpa using hU z⟩, inferInstance⟩ }

  let F : ∀ z : P, (U z : Scheme.{u}) ⟶ Y := fun z => (xU z).1 ≫ ψ.1
  have hF : ∀ i j : P, pullback.fst (𝒰.f i) (𝒰.f j) ≫ F i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ F j := by
    intro i j

    let w : pullback (U i).ι (U j).ι ⟶ Spec (CommRingCat.of k) := pullback.fst (U i).ι (U j).ι ≫ (U i).ι ≫ t₀
    let a : SchemeHomOver w fs := GoodReductionJacobian.schemeHomOverComp (pullback.fst (U i).ι (U j).ι) rfl (xU i)
    let b : SchemeHomOver w fs := GoodReductionJacobian.schemeHomOverComp (pullback.snd (U i).ι (U j).ι)
      (by rw [← Category.assoc, ← pullback.condition, Category.assoc]) (xU j)
    have key := comp_ψ_eq_of_proj_eq H w a b ?_ ?_
    · have := congrArg Subtype.val key
      simpa [a, b, F] using this
    · apply Subtype.ext
      show pullback.fst (U i).ι (U j).ι ≫ (xU i).1 ≫ ν₁.1 = pullback.snd (U i).ι (U j).ι ≫ (xU j).1 ≫ ν₁.1
      have ei : (xU i).1 ≫ ν₁.1 = (U i).ι ≫ u₁.1 := hxU1 i
      have ej : (xU j).1 ≫ ν₁.1 = (U j).ι ≫ u₁.1 := hxU1 j
      rw [ei, ej, ← Category.assoc, ← Category.assoc, pullback.condition]
    · apply Subtype.ext
      show pullback.fst (U i).ι (U j).ι ≫ (xU i).1 ≫ ν₂.1 = pullback.snd (U i).ι (U j).ι ≫ (xU j).1 ≫ ν₂.1
      have ei : (xU i).1 ≫ ν₂.1 = (U i).ι ≫ u₂.1 := hxU2 i
      have ej : (xU j).1 ≫ ν₂.1 = (U j).ι ≫ u₂.1 := hxU2 j
      rw [ei, ej, ← Category.assoc, ← Category.assoc, pullback.condition]

  let g : P ⟶ Y := 𝒰.glueMorphisms F hF
  have hg : ∀ z : P, (U z).ι ≫ g = F z := fun z => 𝒰.ι_glueMorphisms F hF z
  have hgY : g ≫ gY = t₀ := by
    refine 𝒰.hom_ext _ _ fun z => ?_
    show (U z).ι ≫ g ≫ gY = (U z).ι ≫ t₀
    rw [← Category.assoc, hg z]
    show ((xU z).1 ≫ ψ.1) ≫ gY = (U z).ι ≫ t₀
    rw [Category.assoc, ψ.2, (xU z).2]
  let ψbar : SchemeHomOver (prodStr f₁ f₂) gY := ⟨g, hgY⟩

  have hfac : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t fs),
      NeronModelInfra.schemeHomOverComp x ψ =
        NeronModelInfra.schemeHomOverComp (prodPairPt (postComp ν₁ x) (postComp ν₂ x)) ψbar := by
    intro T' t x
    apply Subtype.ext
    show x.1 ≫ ψ.1 = (prodPairPt (postComp ν₁ x) (postComp ν₂ x)).1 ≫ g
    set q : T' ⟶ P := (prodPairPt (postComp ν₁ x) (postComp ν₂ x)).1 with hq
    have hq1 : q ≫ pullback.fst f₁ f₂ = x.1 ≫ ν₁.1 := by rw [hq, prodPairPt_coe, pullback.lift_fst]; rfl
    have hq2 : q ≫ pullback.snd f₁ f₂ = x.1 ≫ ν₂.1 := by rw [hq, prodPairPt_coe, pullback.lift_snd]; rfl
    have hqt : q ≫ t₀ = t := by
      show q ≫ pullback.fst f₁ f₂ ≫ f₁ = t
      rw [← Category.assoc, hq1, Category.assoc, ν₁.2, x.2]

    apply Scheme.hom_ext_of_forall
    intro z'
    refine ⟨q ⁻¹ᵁ (U (q.base z')), by simpa using hU (q.base z'), ?_⟩

    set V := q ⁻¹ᵁ (U (q.base z')) with hV
    let r : (V : Scheme.{u}) ⟶ (U (q.base z') : Scheme.{u}) := q ∣_ (U (q.base z'))
    have hr : r ≫ (U (q.base z')).ι = V.ι ≫ q := morphismRestrict_ι _ _
    let w : (V : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := V.ι ≫ t
    let a : SchemeHomOver w fs := GoodReductionJacobian.schemeHomOverComp V.ι rfl x
    let b : SchemeHomOver w fs := GoodReductionJacobian.schemeHomOverComp r
      (by show r ≫ (U (q.base z')).ι ≫ t₀ = V.ι ≫ t
          rw [← Category.assoc, hr, Category.assoc, hqt]) (xU (q.base z'))
    have key := comp_ψ_eq_of_proj_eq H w a b ?_ ?_
    · have := congrArg Subtype.val key

      have e2 : r ≫ (xU (q.base z')).1 ≫ ψ.1 = V.ι ≫ q ≫ g := by
        rw [show (xU (q.base z')).1 ≫ ψ.1 = F (q.base z') from rfl, ← hg, ← Category.assoc, hr, Category.assoc]
      simpa [a, b, e2] using this
    · apply Subtype.ext
      show V.ι ≫ x.1 ≫ ν₁.1 = r ≫ (xU (q.base z')).1 ≫ ν₁.1
      rw [show (xU (q.base z')).1 ≫ ν₁.1 = (U (q.base z')).ι ≫ u₁.1 from hxU1 _, ← Category.assoc r, hr, hu₁,
        Category.assoc, hq1]
    · apply Subtype.ext
      show V.ι ≫ x.1 ≫ ν₂.1 = r ≫ (xU (q.base z')).1 ≫ ν₂.1
      rw [show (xU (q.base z')).1 ≫ ν₂.1 = (U (q.base z')).ι ≫ u₂.1 from hxU2 _, ← Category.assoc r, hr, hu₂,
        Category.assoc, hq2]

  have huniq : ∀ ψbar' : SchemeHomOver (prodStr f₁ f₂) gY,
      (∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t fs),
        NeronModelInfra.schemeHomOverComp x ψ =
          NeronModelInfra.schemeHomOverComp (prodPairPt (postComp ν₁ x) (postComp ν₂ x)) ψbar') →
      ψbar' = ψbar := by
    intro ψbar' h'
    apply Subtype.ext
    refine 𝒰.hom_ext _ _ fun z => ?_
    show (U z).ι ≫ ψbar'.1 = (U z).ι ≫ g

    have hpair : (prodPairPt (postComp ν₁ (xU z)) (postComp ν₂ (xU z))).1 = (U z).ι := by
      rw [prodPairPt_coe]
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        exact (show (xU z).1 ≫ ν₁.1 = (U z).ι ≫ u₁.1 from hxU1 z).trans (by rw [hu₁])
      · rw [pullback.lift_snd]
        exact (show (xU z).1 ≫ ν₂.1 = (U z).ι ≫ u₂.1 from hxU2 z).trans (by rw [hu₂])
    have e1 := congrArg Subtype.val (h' ((U z).ι ≫ t₀) (xU z))
    have e2 := congrArg Subtype.val (hfac ((U z).ι ≫ t₀) (xU z))
    simp only [NeronModelInfra.schemeHomOverComp_coe, hpair] at e1 e2
    rw [← e1, ← e2]

  have hhom : ∀ {T' : Scheme.{u}} (s : T' ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver s (prodStr f₁ f₂)),
      NeronModelInfra.schemeHomOverComp ((L₁.prod L₂).mul s a b) ψbar =
        LY.mul s (NeronModelInfra.schemeHomOverComp a ψbar) (NeronModelInfra.schemeHomOverComp b ψbar) := by
    intro S s a b
    apply Subtype.ext
    apply Scheme.hom_ext_of_forall
    intro z

    obtain ⟨Ua, hza, α, hα1, hα2⟩ := H.hepi s (prodFstPt a) (prodSndPt a) z
    obtain ⟨Ub, hzb, β, hβ1, hβ2⟩ := H.hepi s (prodFstPt b) (prodSndPt b) z
    refine ⟨Ua ⊓ Ub, ⟨hza, hzb⟩, ?_⟩
    set V : S.Opens := Ua ⊓ Ub with hV
    let ia : (V : Scheme.{u}) ⟶ (Ua : Scheme.{u}) := S.homOfLE inf_le_left
    let ib : (V : Scheme.{u}) ⟶ (Ub : Scheme.{u}) := S.homOfLE inf_le_right
    have hia : ia ≫ Ua.ι = V.ι := S.homOfLE_ι _
    have hib : ib ≫ Ub.ι = V.ι := S.homOfLE_ι _
    let w : (V : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := V.ι ≫ s

    let αV : SchemeHomOver w fs := GoodReductionJacobian.schemeHomOverComp ia (by rw [← Category.assoc, hia]) α
    let βV : SchemeHomOver w fs := GoodReductionJacobian.schemeHomOverComp ib (by rw [← Category.assoc, hib]) β

    let aV : SchemeHomOver w (prodStr f₁ f₂) := GoodReductionJacobian.schemeHomOverComp V.ι rfl a
    let bV : SchemeHomOver w (prodStr f₁ f₂) := GoodReductionJacobian.schemeHomOverComp V.ι rfl b
    have haV : aV = prodPairPt (postComp ν₁ αV) (postComp ν₂ αV) := by
      apply prodPt_ext
      · rw [prodFstPt_prodPairPt]; apply Subtype.ext
        show (V.ι ≫ a.1) ≫ pullback.fst f₁ f₂ = (ia ≫ α.1) ≫ ν₁.1
        rw [Category.assoc, Category.assoc, show α.1 ≫ ν₁.1 = Ua.ι ≫ (prodFstPt a).1 from hα1, ← Category.assoc ia, hia]; rfl
      · rw [prodSndPt_prodPairPt]; apply Subtype.ext
        show (V.ι ≫ a.1) ≫ pullback.snd f₁ f₂ = (ia ≫ α.1) ≫ ν₂.1
        rw [Category.assoc, Category.assoc, show α.1 ≫ ν₂.1 = Ua.ι ≫ (prodSndPt a).1 from hα2, ← Category.assoc ia, hia]; rfl
    have hbV : bV = prodPairPt (postComp ν₁ βV) (postComp ν₂ βV) := by
      apply prodPt_ext
      · rw [prodFstPt_prodPairPt]; apply Subtype.ext
        show (V.ι ≫ b.1) ≫ pullback.fst f₁ f₂ = (ib ≫ β.1) ≫ ν₁.1
        rw [Category.assoc, Category.assoc, show β.1 ≫ ν₁.1 = Ub.ι ≫ (prodFstPt b).1 from hβ1, ← Category.assoc ib, hib]; rfl
      · rw [prodSndPt_prodPairPt]; apply Subtype.ext
        show (V.ι ≫ b.1) ≫ pullback.snd f₁ f₂ = (ib ≫ β.1) ≫ ν₂.1
        rw [Category.assoc, Category.assoc, show β.1 ≫ ν₂.1 = Ub.ι ≫ (prodSndPt b).1 from hβ2, ← Category.assoc ib, hib]; rfl

    have eA : NeronModelInfra.schemeHomOverComp aV ψbar = NeronModelInfra.schemeHomOverComp αV ψ := by
      rw [haV, ← hfac]
    have eB : NeronModelInfra.schemeHomOverComp bV ψbar = NeronModelInfra.schemeHomOverComp βV ψ := by
      rw [hbV, ← hfac]
    have eAB : NeronModelInfra.schemeHomOverComp ((L₁.prod L₂).mul w aV bV) ψbar =
        NeronModelInfra.schemeHomOverComp (Ls.mul w αV βV) ψ := by
      rw [haV, hbV, RelativeGroupLaw.prodPairPt_mul_prodPairPt, ← H.hν₁, ← H.hν₂, ← hfac]

    have lhs : V.ι ≫ ((L₁.prod L₂).mul s a b).1 ≫ g =
        (NeronModelInfra.schemeHomOverComp ((L₁.prod L₂).mul w aV bV) ψbar).1 := by
      have := (L₁.prod L₂).mul_natural s w V.ι rfl a b
      rw [NeronModelInfra.schemeHomOverComp_coe, ← this]; rfl
    have rhs : V.ι ≫ (LY.mul s (NeronModelInfra.schemeHomOverComp a ψbar) (NeronModelInfra.schemeHomOverComp b ψbar)).1 =
        (LY.mul w (NeronModelInfra.schemeHomOverComp aV ψbar) (NeronModelInfra.schemeHomOverComp bV ψbar)).1 := by
      have := LY.mul_natural s w V.ι rfl (NeronModelInfra.schemeHomOverComp a ψbar) (NeronModelInfra.schemeHomOverComp b ψbar)
      rw [← comp_restrict ψbar V.ι rfl a, ← comp_restrict ψbar V.ι rfl b] at this
      exact congrArg Subtype.val this
    show V.ι ≫ ((L₁.prod L₂).mul s a b).1 ≫ g = V.ι ≫ (LY.mul s _ _).1
    rw [lhs, rhs, eAB, eA, eB, H.hψ]
  exact ⟨ψbar, ⟨hfac, hhom⟩, fun ψbar' h' => huniq ψbar' h'.1⟩

end K6Core

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
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (hXred : IsReduced (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))

    (T : Scheme.{0}) (tT : T ⟶ Spec (CommRingCat.of k)) (LT : RelativeGroupLaw k tT)
    (jT : SchemeHomOver tT (D.baseChange k).toBase)
    (eT : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin (n - 1) → Rˣ) ≃ SchemeHomOver (specMap k R) tT)
    (hjT : IsClosedImmersion jT.1)
    (hjTmul : ∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s tT),
        NeronModelInfra.schemeHomOverComp (LT.mul s x y) jT =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul s
            (NeronModelInfra.schemeHomOverComp x jT) (NeronModelInfra.schemeHomOverComp y jT))
    (hker : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (D.baseChange k).toBase),
        (∃ y : SchemeHomOver t tT, NeronModelInfra.schemeHomOverComp y jT = x) ↔
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x =
              (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).one t ∧
            postComp ν₂ x = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).one t))
    (heT_mul : ∀ (R : Type) [CommRing R] [Algebra k R] (u v : Fin (n - 1) → Rˣ),
        eT R (u * v) = LT.mul _ (eT R u) (eT R v))
    (heT_nat : ∀ (R R' : Type) [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R'] (a : R →ₐ[k] R') (u : Fin (n - 1) → Rˣ),
        (eT R' (fun i => Units.map a.toRingHom.toMonoidHom (u i))).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eT R u).1)
    (hepi : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x₁ : SchemeHomOver t D₁.toBase) (x₂ : SchemeHomOver t D₂.toBase)
        (z : T'), ∃ (U : T'.Opens) (_ : z ∈ U) (x : SchemeHomOver (U.ι ≫ t) (D.baseChange k).toBase),
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x).1 = U.ι ≫ x₁.1 ∧
          (postComp ν₂ x).1 = U.ι ≫ x₂.1)

    (Y : Scheme.{0}) (gY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated gY] (LY : RelativeGroupLaw k gY)
    (ψ : SchemeHomOver (D.baseChange k).toBase gY)

    (hψmul : ∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s (D.baseChange k).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul s x y) ψ =
          LY.mul s (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ))

    (hψT : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (y : SchemeHomOver t tT),
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp y jT) ψ = LY.one t) :
    ∃! ψbar : SchemeHomOver (prodStr D₁.toBase D₂.toBase) gY,

      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (D.baseChange k).toBase),
        NeronModelInfra.schemeHomOverComp x ψ =
          NeronModelInfra.schemeHomOverComp
            (prodPairPt (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x) (postComp ν₂ x)) ψbar) ∧

      (∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver s (prodStr D₁.toBase D₂.toBase)),
        NeronModelInfra.schemeHomOverComp
            (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).prod
              (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some)).mul s a b) ψbar =
          LY.mul s (NeronModelInfra.schemeHomOverComp a ψbar) (NeronModelInfra.schemeHomOverComp b ψbar)) := by
  classical
  have H : K6Core.Hyp
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps)
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some)
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some)
      LY (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) ν₂ jT ψ :=
    { hν₁ := fun s x y =>
        AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_pullbackHom_mul i₁.1 i₁.2 hε₁ hreps hrep₁.some s x y
      hν₂ := fun s x y =>
        AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_mul_of_classifies_rigidify_pullback_curveChange
          i₂.1 i₂.2 hreps hrep₂.some ν₂ (fun t a => hν₂ t a) s x y
      hψ := fun s x y => hψmul s x y
      hker := fun t x hx => (hker t x).mpr hx
      hepi := fun t x₁ x₂ z => hepi t x₁ x₂ z
      hψT := fun t y => hψT t y }
  exact K6Core.existsUnique_factor H

#print axioms solution

end S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul (solution)
