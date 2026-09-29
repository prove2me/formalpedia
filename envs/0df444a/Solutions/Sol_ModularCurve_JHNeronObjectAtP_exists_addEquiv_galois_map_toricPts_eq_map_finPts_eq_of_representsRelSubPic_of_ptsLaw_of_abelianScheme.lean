-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f10240e7-78c6-52f2-b50d-f7320841ff65

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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

noncomputable section

namespace OT

namespace RepIso

universe u

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}

theorem inv_over (e : C ≅ C') (he : e.hom ≫ c' = c) : e.inv ≫ c = c' := by
  rw [← he, Iso.inv_hom_id_assoc]

theorem inv_section (e : C ≅ C') (hε : ε.1 ≫ e.hom = ε'.1) : ε'.1 ≫ e.inv = ε.1 := by
  rw [← hε, Category.assoc, Iso.hom_inv_id, Category.comp_id]

noncomputable def isoOfIso (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    D.P ≅ D'.P where
  hom := (RepresentsRelSubPic.pullbackHom e.inv (inv_over e he) (inv_section e hε) h h').1
  inv := (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).1
  hom_inv_id := (AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_inv_comp_pullbackHom_hom_of_iso
    e he (inv_over e he) hε (inv_section e hε) h h').1
  inv_hom_id := (AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_inv_comp_pullbackHom_hom_of_iso
    e he (inv_over e he) hε (inv_section e hε) h h').2

theorem isoOfIso_hom_over (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (isoOfIso e he hε h h').hom ≫ D'.toBase = D.toBase :=
  (RepresentsRelSubPic.pullbackHom e.inv (inv_over e he) (inv_section e hε) h h').2

theorem isoOfIso_inv_over (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (isoOfIso e he hε h h').inv ≫ D.toBase = D'.toBase :=
  (RepresentsRelSubPic.pullbackHom e.hom he hε h' h).2

theorem isoOfIso_hom_eq (e : C ≅ C') (he : e.hom ≫ c' = c) (hε : ε.1 ≫ e.hom = ε'.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (isoOfIso e he hε h h').hom = (RepresentsRelSubPic.pullbackHom e.inv (inv_over e he) (inv_section e hε) h h').1 := rfl

section PullbackHomMul

open scoped CategoryTheory.MonObj

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}

theorem nonempty_tensor_pullbackCurve_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L M : RigidifiedLineBundle c ε t) :
    Nonempty (((L.tensor M).pullbackCurve f hf hε).L ≅ ((L.pullbackCurve f hf hε).tensor (M.pullbackCurve f hf hε)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩

theorem nonempty_pullbackAlong_mul_iso (P : SubPicGroupCondition c ε) (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)).L ≅
      ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)).L) := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op (Over.mk t))
  have key := congrArg Subtype.val (h.homEquiv_mul (Over.mk t) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b))

  have hl : (h.representableBy.homEquiv (schemeHomOverToOverHom a * schemeHomOverToOverHom b)).1 =
      Quotient.mk _ (h.poincare.pullbackAlong (h.relativeGroupLaw.mul t a b)) := rfl
  have hr : ((h.representableBy.homEquiv (schemeHomOverToOverHom a)) *
      (h.representableBy.homEquiv (schemeHomOverToOverHom b))).1 =
      Quotient.mk _ ((h.poincare.pullbackAlong a).tensor (h.poincare.pullbackAlong b)) := rfl
  rw [hl, hr] at key
  exact Quotient.exact key

theorem nonempty_pullbackAlong_postComp_pullbackHom_iso (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') x)).L ≅
      ((h.poincare.pullbackAlong x).pullbackCurve f hf hε).L) := by
  have hPx : (algEquivZeroCut c ε).P t (h.poincare.pullbackAlong x) :=
    (algEquivZeroCut c ε).pullback_mem _ _ x _ h.poincare_mem
  have hx : x = h.classify t (h.poincare.pullbackAlong x) hPx := h.classify_unique t _ hPx x ⟨Iso.refl _⟩
  have hx' : postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') x =
      h'.classify t ((h.poincare.pullbackAlong x).pullbackCurve f hf hε)
        (FibrewiseAlgEquivZero.pullbackCurve f hf hε hPx) := by
    conv_lhs => rw [hx]
    exact RepresentsRelSubPic.postComp_pullbackHom_classify f hf hε h h' t _ hPx
  rw [hx']
  exact h'.classify_spec t _ _

theorem postComp_pullbackHom_mul (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t D.toBase) :
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h')
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a)
        (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') b) := by
  refine h'.ext_of_iso t _ _ ?_
  obtain ⟨i1⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t a b)
  obtain ⟨i2⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c ε) h t a b
  obtain ⟨i3⟩ := nonempty_tensor_pullbackCurve_iso f hf hε (h.poincare.pullbackAlong a) (h.poincare.pullbackAlong b)
  obtain ⟨ia⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t a
  obtain ⟨ib⟩ := nonempty_pullbackAlong_postComp_pullbackHom_iso f hf hε h h' t b
  obtain ⟨i4⟩ := nonempty_pullbackAlong_mul_iso (algEquivZeroGroupCut c' ε') h' t
    (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') a) (postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') b)
  exact ⟨i1 ≪≫ (Scheme.Modules.pullback _).mapIso i2 ≪≫ i3 ≪≫ (ia.symm ⊗ᵢ ib.symm) ≪≫ i4.symm⟩

end PullbackHomMul

end RepIso

section laws

variable {R : Type} [CommRing R] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)}

theorem mul_eq_mul_of_pts (L Lc : RelativeGroupLaw R g) {V : Type} [Add V] {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ _}
    (pts : V ≃ SchemeHomOver s g)
    (hL : ∀ v w : V, pts (v + w) = L.mul _ (pts v) (pts w)) (hLc : ∀ v w : V, pts (v + w) = Lc.mul _ (pts v) (pts w)) :
    ∀ a b : SchemeHomOver s g, L.mul s a b = Lc.mul s a b := by
  intro a b
  obtain ⟨v, rfl⟩ := pts.surjective a
  obtain ⟨w, rfl⟩ := pts.surjective b
  rw [← hL, hLc]

end laws

section Main

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hpts_law : ∀ x y : JH M H, O.pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f)
    (hpts_law' : ∀ x y : JH M H, O'.pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul _ (O'.pts x) (O'.pts y))

def psiIso : O.G ≅ O'.G :=
  RepIso.isoOfIso (Iso.refl _) (Category.id_comp _) (Category.comp_id _) hD hD'

def psi : SchemeHomOver O.g O'.g :=
  ⟨(psiIso p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').hom,
    RepIso.isoOfIso_hom_over (Iso.refl _) (Category.id_comp _) (Category.comp_id _) hD hD'⟩

def psiInv : SchemeHomOver O'.g O.g :=
  ⟨(psiIso p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').inv,
    RepIso.isoOfIso_inv_over (Iso.refl _) (Category.id_comp _) (Category.comp_id _) hD hD'⟩

@[scoped simp] theorem psi_val : (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 = (psiIso p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').hom := rfl
@[scoped simp] theorem psiInv_val : (psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 = (psiIso p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').inv := rfl

theorem psi_comp_psiInv : (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 ≫ (psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 = 𝟙 _ :=
  (psiIso p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').hom_inv_id

theorem psiInv_comp_psi : (psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 ≫ (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 = 𝟙 _ :=
  (psiIso p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').inv_hom_id

theorem psi_mul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a b : SchemeHomOver t O.g) :
    NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t a b)
        (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD') =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul t
        (NeronModelInfra.schemeHomOverComp a (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD'))
        (NeronModelInfra.schemeHomOverComp b (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD')) :=
  RepIso.postComp_pullbackHom_mul (Iso.refl _).inv (RepIso.inv_over (Iso.refl _) (Category.id_comp _))
    (RepIso.inv_section (Iso.refl _) (Category.comp_id _)) hD hD' t a b

include hpts_law in

theorem law_agree : ∀ a b : SchemeHomOver (genPt p) O.g,
    O.L.mul _ a b = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ a b :=
  mul_eq_mul_of_pts O.L _ O.pts O.pts_add hpts_law

def psiPt (x : SchemeHomOver (genPt p) O.g) : SchemeHomOver (genPt p) O'.g :=
  NeronModelInfra.schemeHomOverComp x (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD')

def psiInvPt (y : SchemeHomOver (genPt p) O'.g) : SchemeHomOver (genPt p) O.g :=
  NeronModelInfra.schemeHomOverComp y (psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD')

theorem psiInvPt_psiPt (x : SchemeHomOver (genPt p) O.g) :
    psiInvPt p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' (psiPt p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' x) = x := by
  apply Subtype.ext
  simp only [psiInvPt, psiPt, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, psi_val, psiInv_val, Iso.hom_inv_id,
    Category.comp_id]

theorem psiPt_psiInvPt (y : SchemeHomOver (genPt p) O'.g) :
    psiPt p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' (psiInvPt p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' y) = y := by
  apply Subtype.ext
  simp only [psiInvPt, psiPt, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, psi_val, psiInv_val, Iso.inv_hom_id,
    Category.comp_id]

def eEquiv : JH M H ≃ JH M H where
  toFun x := O'.pts.symm (psiPt p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' (O.pts x))
  invFun y := O.pts.symm (psiInvPt p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' (O'.pts y))
  left_inv x := by simp [psiInvPt_psiPt]
  right_inv y := by simp [psiPt_psiInvPt]

theorem pts'_eEquiv (x : JH M H) :
    (O'.pts (eEquiv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' x)).1 = (O.pts x).1 ≫ (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 := by
  simp [eEquiv, psiPt]

include hpts_law hpts_law' in

theorem eEquiv_add (x y : JH M H) :
    eEquiv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' (x + y) =
      eEquiv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' x + eEquiv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' y := by
  apply O'.pts.injective
  rw [hpts_law']
  simp only [eEquiv, Equiv.coe_fn_mk, Equiv.apply_symm_apply]
  rw [hpts_law, psiPt, psi_mul]
  rfl

include hpts_law hpts_law' in

def e : JH M H ≃+ JH M H :=
  { eEquiv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' with
    map_add' := eEquiv_add p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' }

include hpts_law hpts_law' in
theorem e_apply (x : JH M H) : e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' x =
    O'.pts.symm (psiPt p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' (O.pts x)) := rfl

include hpts_law hpts_law' in

theorem pts'_e (x : JH M H) :
    (O'.pts (e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' x)).1 =
      (O.pts x).1 ≫ (psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 :=
  pts'_eEquiv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' x

include hpts_law hpts_law' in

theorem e_galois (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H) :
    e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' (σ • x) =
      σ • e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' x := by
  apply O'.pts.injective
  apply Subtype.ext
  rw [pts'_e, O.pts_galois, O'.pts_galois, pts'_e, Category.assoc]

end Main

end OT
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme.OT"

namespace OT

section L45

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hpts_law : ∀ x y : JH M H, O.pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f)
    (hpts_law' : ∀ x y : JH M H, O'.pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul _ (O'.pts x) (O'.pts y))

theorem sigmaA_eq : Λ.σA = Λ'.σA := by

  obtain ⟨χ, hχ⟩ := Spec.map_surjective Λ.σA
  obtain ⟨χ', hχ'⟩ := Spec.map_surjective Λ'.σA
  have h1 := Λ.hσA
  have h2 := Λ'.hσA
  rw [← hχ] at h1
  rw [← hχ'] at h2
  change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map χ = Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (AlgebraicClosure ℚ))) at h1
  change Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map χ' = Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) (AlgebraicClosure ℚ))) at h2
  rw [← Spec.map_comp] at h1 h2
  have e1 := Spec.map_injective h1
  have e2 := Spec.map_injective h2
  have hχχ' : χ = χ' := by
    ext x

    have := congrArg (fun f : CommRingCat.of (baseRing p) ⟶ CommRingCat.of (AlgebraicClosure ℚ) => f.hom x) (e1.trans e2.symm)
    simpa using this
  rw [← hχ, ← hχ', hχχ']

theorem extendsToPlace_iff (x : JH M H) :
    ExtendsToPlace A Λ'.σA (O'.pts (OT.e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' x)) ↔
      ExtendsToPlace A Λ.σA (O.pts x) := by
  have hσ := sigmaA_eq p M H hpM A Λ Λ'
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨⟨s.1 ≫ (OT.psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1, ?_⟩, ?_⟩
    · rw [Category.assoc, (OT.psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').2, s.2, hσ]
    · have h1 := OT.pts'_e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' x
      have h2 := OT.psi_comp_psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD'
      calc (O.pts x).1 = (O.pts x).1 ≫ ((OT.psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 ≫
              (OT.psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1) := by rw [h2, Category.comp_id]
        _ = (barPt A ≫ s.1) ≫ (OT.psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 := by
              rw [← Category.assoc, ← h1, hs]
        _ = barPt A ≫ s.1 ≫ (OT.psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1 := by rw [Category.assoc]
  · rintro ⟨s, hs⟩
    refine ⟨⟨s.1 ≫ (OT.psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1, ?_⟩, ?_⟩
    · rw [Category.assoc, (OT.psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').2, s.2, hσ]
    · rw [OT.pts'_e, hs, Category.assoc]

theorem finPts_map (m : ℕ) :
    O'.finPts m = (O.finPts m).map (OT.e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law').toAddMonoidHom := by
  classical
  set e := OT.e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' with he
  unfold JHNeronObjectAtP.finPts
  rw [AddMonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, AddMonoidHom.coe_coe, AddEquiv.coe_toAddMonoidHom]
  constructor
  · rintro ⟨hy, hext⟩
    refine ⟨e.symm y, ⟨?_, ?_⟩, by simp⟩
    ·
      rw [AlgebraicCurve.Pic0.mem_torsion] at hy ⊢
      apply e.injective
      rw [map_zsmul, AddEquiv.apply_symm_apply, hy, map_zero]
    · have := (extendsToPlace_iff p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' (e.symm y)).1
      rw [he, AddEquiv.apply_symm_apply] at this
      exact this hext
  · rintro ⟨x, ⟨hx, hext⟩, rfl⟩
    refine ⟨?_, (extendsToPlace_iff p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' x).2 hext⟩
    rw [AlgebraicCurve.Pic0.mem_torsion] at hx ⊢
    rw [← map_zsmul, hx, map_zero]

theorem toric_rigid_of_TR (m : ℕ) (hm : 0 < m)
    (hTR : ∃ a : (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) ≃ (muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
        ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
          (O'.pts (O'.toricPoint m hm (a χ))).1 = (O.pts (O.toricPoint m hm χ)).1 ≫ (OT.psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD').1) :
    ∃ a : (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) ≃ (muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      ∀ χ, OT.e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' (O.toricPoint m hm χ) = O'.toricPoint m hm (a χ) := by
  obtain ⟨a, ha⟩ := hTR
  refine ⟨a, fun χ => ?_⟩
  apply O'.pts.injective
  apply Subtype.ext
  rw [OT.pts'_e, ha]

include hpM2 hΛ' in

theorem toric_rigid (m : ℕ) (hm : 0 < m) :
    ∃ a : (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) ≃ (muCoord ↥A O'.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      ∀ χ, OT.e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' (O.toricPoint m hm χ) = O'.toricPoint m hm (a χ) :=
  toric_rigid_of_TR p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' m hm
    (ModularCurve.JHNeronObjectAtP.exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
      p M H hpM hpM2 hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hΛ' hpts_law'
      (OT.psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD') (OT.psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD')
      (OT.psi_comp_psiInv p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD') (OT.psiInv_comp_psi p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD')
      (fun s x y => OT.psi_mul p M H hpM hj 𝔛 A hA Λ O hD Λ' O' hD' s x y) m hm)

include hpM2 hΛ' in

theorem toricPts_map (m : ℕ) (hm : 0 < m) :
    O'.toricPts m = (O.toricPts m).map (OT.e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law').toAddMonoidHom := by
  classical
  obtain ⟨a, ha⟩ := toric_rigid p M H hpM hpM2 hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hΛ' hpts_law' m hm
  unfold JHNeronObjectAtP.toricPts
  rw [dif_pos hm, dif_pos hm, AddMonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image, AddMonoidHom.coe_coe, AddEquiv.coe_toAddMonoidHom]
  constructor
  · rintro ⟨χ', rfl⟩
    exact ⟨O.toricPoint m hm (a.symm χ'), ⟨a.symm χ', rfl⟩, by rw [ha, Equiv.apply_symm_apply]⟩
  · rintro ⟨x, ⟨χ, rfl⟩, rfl⟩
    exact ⟨a χ, (ha χ).symm⟩

end L45
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme.OT"

end OT
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme.OT"

end
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme.OT"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f)
    (hpts_law' : ∀ x y : JH M H,
        O'.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD').mul _ (O'.pts x) (O'.pts y)) :
    ∃ e : JH M H ≃+ JH M H,
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H), e (σ • x) = σ • e x) ∧
      (∀ m : ℕ, 0 < m →
        (O'.toricPts m) = (O.toricPts m).map e.toAddMonoidHom ∧
        (O'.finPts m) = (O.finPts m).map e.toAddMonoidHom) :=
  ⟨OT.e p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law',
    OT.e_galois p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law',
    fun m hm => ⟨OT.toricPts_map p M H hpM hpM2 hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hΛ' hpts_law' m hm,
      OT.finPts_map p M H hpM hj 𝔛 A hA Λ O hD hpts_law Λ' O' hD' hpts_law' m⟩⟩

end S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_ptsLaw_of_abelianScheme (solution)
