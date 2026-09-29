-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9fa6959b-d219-58f6-9be0-89c5da23f833

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian TopologicalSpace Topology"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "IsCommutative pointGroup one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul smooth_of_geometricallyReduced_of_locallyOfFiniteType exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
namespace ReducedIdentityComponent
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Reduced

open AlgebraicGeometry.Scheme.IdealSheafData

abbrev Gr (G : Scheme.{u}) : Scheme.{u} := (vanishingIdeal (⊤ : Closeds G)).subscheme

abbrev ιr (G : Scheme.{u}) : Gr G ⟶ G := (vanishingIdeal (⊤ : Closeds G)).subschemeι

scoped instance isReduced_Gr (G : Scheme.{u}) : IsReduced (Gr G) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
    (⊤ : Closeds G)).1

theorem range_ιr (G : Scheme.{u}) : Set.range (ιr G) = Set.univ := by
  rw [range_subschemeι]
  apply Set.eq_univ_of_univ_subset
  have h : (⊤ : Closeds G) ≤ (vanishingIdeal (⊤ : Closeds G)).support :=
    le_support_iff_le_vanishingIdeal.mpr le_rfl
  exact h

theorem surjective_ιr (G : Scheme.{u}) : Function.Surjective (ιr G) :=
  Set.range_eq_univ.mp (range_ιr G)

theorem isHomeomorph_ιr (G : Scheme.{u}) : IsHomeomorph (ιr G) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(ιr G).isClosedEmbedding.isEmbedding, surjective_ιr G⟩

def liftr {G T : Scheme.{u}} [IsReduced T] (g : T ⟶ G) : T ⟶ Gr G :=
  IsClosedImmersion.lift (ιr G) g (by
    rw [ker_subschemeι]
    exact (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (⊤ : Closeds G)).2 g (fun _ _ => trivial))

@[reassoc (attr := simp)]
theorem liftr_ι {G T : Scheme.{u}} [IsReduced T] (g : T ⟶ G) : liftr g ≫ ιr G = g :=
  IsClosedImmersion.lift_fac _ _ _

end Reduced

section Law

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  (L : RelativeGroupLaw k f)

abbrev fr (f : G ⟶ Spec (CommRingCat.of k)) : Gr G ⟶ Spec (CommRingCat.of k) := ιr G ≫ f

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) *
      GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    show L.mul t' _ _ = L.one t'
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural]
  exact eq_inv_of_mul_eq_one_left h

def toG {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fr f)) :
    SchemeHomOver t f :=
  ⟨x.1 ≫ ιr G, by rw [Category.assoc]; exact x.2⟩

@[scoped simp]
theorem toG_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fr f)) :
    (toG x).1 = x.1 ≫ ιr G := rfl

theorem toG_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (fr f)) :
    toG x = NeronModelInfra.schemeHomOverComp x (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f) := rfl

theorem toG_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (toG (f := f) (T := T) (t := t)) := by
  intro x y h
  exact Subtype.ext ((cancel_mono (ιr G)).mp (congrArg Subtype.val h))

theorem toG_transition {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (fr f)) :
    toG (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (toG x) :=
  Subtype.ext (Category.assoc _ _ _)

def liftPt {T : Scheme.{u}} [IsReduced T] {t : T ⟶ Spec (CommRingCat.of k)}
    (y : SchemeHomOver t f) : SchemeHomOver t (fr f) :=
  ⟨liftr y.1, by rw [liftr_ι_assoc]; exact y.2⟩

@[scoped simp]
theorem toG_liftPt {T : Scheme.{u}} [IsReduced T] {t : T ⟶ Spec (CommRingCat.of k)}
    (y : SchemeHomOver t f) : toG (liftPt y) = y :=
  Subtype.ext (liftr_ι _)

theorem toG_surjective {T : Scheme.{u}} [IsReduced T] {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Surjective (toG (f := f) (T := T) (t := t)) :=
  fun y => ⟨liftPt y, toG_liftPt y⟩

variable [PerfectField k] [LocallyOfFiniteType f]

theorem geometricallyReduced_fr : GeometricallyReduced (fr f) :=
  AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField (fr f)

theorem isReduced_pullback_fr : IsReduced (pullback (fr f) (fr f)) := by
  haveI : GeometricallyReduced (fr f) := geometricallyReduced_fr
  haveI : IsLocallyNoetherian (Gr G) := LocallyOfFiniteType.isLocallyNoetherian (fr f)
  infer_instance

def M : pullback (fr f) (fr f) ⟶ G :=
  (L.mul (pullback.fst (fr f) (fr f) ≫ fr f)
    ⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp⟩
    ⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa using pullback.condition.symm⟩).1

def Mr : pullback (fr f) (fr f) ⟶ Gr G :=
  haveI : IsReduced (pullback (fr f) (fr f)) := isReduced_pullback_fr
  liftr (M L)

@[reassoc]
theorem Mr_ι : Mr L ≫ ιr G = M L := by
  haveI : IsReduced (pullback (fr f) (fr f)) := isReduced_pullback_fr
  exact liftr_ι _

def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (fr f)) :
    SchemeHomOver t (fr f) :=
  ⟨pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ Mr L, by
    have h := (L.mul (pullback.fst (fr f) (fr f) ≫ fr f)
      ⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp⟩
      ⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa using pullback.condition.symm⟩).2
    rw [Category.assoc, Mr_ι_assoc, M, h, pullback.lift_fst_assoc]
    exact x.2⟩

theorem toG_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (fr f)) :
    toG (mulPt L t x y) = L.mul t (toG x) (toG y) := by
  apply Subtype.ext
  rw [toG_coe]
  change (pullback.lift x.1 y.1 _ ≫ Mr L) ≫ ιr G = _
  rw [Category.assoc, Mr_ι, M]
  have hψ : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ pullback.fst (fr f) (fr f) ≫ fr f = t := by
    rw [pullback.lift_fst_assoc]; exact x.2
  have h := L.mul_natural (pullback.fst (fr f) (fr f) ≫ fr f) t
    (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
    ⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp⟩
    ⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa using pullback.condition.symm⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
      (⟨pullback.fst (fr f) (fr f) ≫ ιr G, by simp⟩ : SchemeHomOver _ f) = toG x :=
    Subtype.ext (by
      rw [GoodReductionJacobian.schemeHomOverComp_coe, toG_coe, pullback.lift_fst_assoc])
  have h2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hψ
      (⟨pullback.snd (fr f) (fr f) ≫ ιr G, by simpa using pullback.condition.symm⟩ :
        SchemeHomOver _ f) = toG y :=
    Subtype.ext (by
      rw [GoodReductionJacobian.schemeHomOverComp_coe, toG_coe, pullback.lift_snd_assoc])
  rw [h1, h2] at h
  exact congrArg Subtype.val h

def er : Spec (CommRingCat.of k) ⟶ Gr G := liftr (L.one (𝟙 _)).1

@[reassoc]
theorem er_ι : er L ≫ ιr G = (L.one (𝟙 _)).1 := liftr_ι _

def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (fr f) :=
  ⟨t ≫ er L, by
    rw [Category.assoc, er_ι_assoc, (L.one (𝟙 _)).2, Category.comp_id]⟩

theorem toG_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toG (onePt L t) = L.one t := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  apply Subtype.ext
  rw [toG_coe]
  change (t ≫ er L) ≫ ιr G = _
  rw [Category.assoc, er_ι, ← h]
  rfl

def jr : Gr G ⟶ Gr G := liftr (L.inv (fr f) ⟨ιr G, rfl⟩).1

@[reassoc]
theorem jr_ι : jr L ≫ ιr G = (L.inv (fr f) ⟨ιr G, rfl⟩).1 := liftr_ι _

def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (fr f)) :
    SchemeHomOver t (fr f) :=
  ⟨x.1 ≫ jr L, by
    rw [Category.assoc, jr_ι_assoc, (L.inv (fr f) ⟨ιr G, rfl⟩).2]
    exact x.2⟩

theorem toG_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t (fr f)) : toG (invPt L t x) = L.inv t (toG x) := by
  have h := inv_natural L (fr f) t x.1 x.2 ⟨ιr G, rfl⟩
  have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f) =
      toG x := Subtype.ext rfl
  rw [h1] at h
  apply Subtype.ext
  rw [toG_coe, ← h]
  change (x.1 ≫ jr L) ≫ ιr G = _
  rw [Category.assoc, jr_ι]
  rfl

def lawr : RelativeGroupLaw k (fr f) where
  mul t x y := mulPt L t x y
  one t := onePt L t
  inv t x := invPt L t x
  mul_assoc t x y z := by
    apply toG_injective
    simp only [toG_mulPt]
    exact L.mul_assoc t _ _ _
  one_mul t x := by
    apply toG_injective
    simp only [toG_mulPt, toG_onePt]
    exact L.one_mul t _
  mul_one t x := by
    apply toG_injective
    simp only [toG_mulPt, toG_onePt]
    exact L.mul_one t _
  inv_mul_cancel t x := by
    apply toG_injective
    simp only [toG_mulPt, toG_invPt, toG_onePt]
    exact L.inv_mul_cancel t _
  mul_natural t t' ψ hψ x y := by
    apply toG_injective
    rw [toG_transition]
    simp only [toG_mulPt]
    rw [L.mul_natural t t' ψ hψ, toG_transition, toG_transition]

theorem toG_lawr_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t (fr f)) :
    toG ((lawr L).mul t x y) = L.mul t (toG x) (toG y) :=
  toG_mulPt L t x y

theorem toG_lawr_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toG ((lawr L).one t) = L.one t :=
  toG_onePt L t

theorem hom_ιr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (fr f)) :
    NeronModelInfra.schemeHomOverComp ((lawr L).mul t x y) (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f))
        (NeronModelInfra.schemeHomOverComp y (⟨ιr G, rfl⟩ : SchemeHomOver (fr f) f)) :=
  toG_lawr_mul L t x y

theorem isCommutative_lawr (hc : L.IsCommutative) : (lawr L).IsCommutative := by
  intro T t x y
  apply toG_injective
  rw [toG_lawr_mul, toG_lawr_mul, hc t]

theorem smooth_fr (L : RelativeGroupLaw k f) : Smooth (fr f) :=
  haveI : GeometricallyReduced (fr f) := geometricallyReduced_fr
  GoodReductionJacobian.RelativeGroupLaw.smooth_of_geometricallyReduced_of_locallyOfFiniteType (lawr L)

end Law

section Cast

variable {k : Type u} [Field k]

def castLaw {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) : RelativeGroupLaw k f₂ := e ▸ L

theorem castLaw_mul_val {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x y : SchemeHomOver t f₂) :
    ((castLaw e L).mul t x y).1 =
      (L.mul t ⟨x.1, by rw [e]; exact x.2⟩ ⟨y.1, by rw [e]; exact y.2⟩).1 := by
  subst e
  rfl

theorem isCommutative_castLaw {X : Scheme.{u}} {f₁ f₂ : X ⟶ Spec (CommRingCat.of k)} (e : f₁ = f₂)
    (L : RelativeGroupLaw k f₁) (hc : L.IsCommutative) : (castLaw e L).IsCommutative := by
  subst e
  exact hc

end Cast

section Topo

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

theorem image_connectedComponent_of_isHomeomorph {φ : α → β} (hφ : IsHomeomorph φ) (a : α) :
    φ '' connectedComponent a = connectedComponent (φ a) := by
  have h := hφ.homeomorph.image_connectedComponentIn (s := Set.univ) (x := a) (Set.mem_univ a)
  rw [Set.image_univ, connectedComponentIn_univ] at h
  have hr : Set.range (hφ.homeomorph φ) = Set.univ := (hφ.homeomorph φ).surjective.range_eq
  rw [hr, connectedComponentIn_univ] at h
  exact h

end Topo

end GoodReductionJacobian.RelativeGroupLaw.ReducedIdentityComponent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian.RelativeGroupLaw.ReducedIdentityComponent"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField.GoodReductionJacobian.RelativeGroupLaw.ReducedIdentityComponent"

open GoodReductionJacobian.RelativeGroupLaw.ReducedIdentityComponent in
theorem solution
    (k : Type u) [Field k] [PerfectField k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] (L : RelativeGroupLaw k f) :
    ∃ (G₀ : Scheme.{u}) (i : G₀ ⟶ G) (L₀ : RelativeGroupLaw k (i ≫ f)) (n : ℕ),
      IsClosedImmersion i ∧ IrreducibleSpace G₀ ∧ SmoothOfRelativeDimension n (i ≫ f) ∧
      GeometricallyIrreducible (i ≫ f) ∧
      IsOpen (Set.range i) ∧
      Set.range i =
        connectedComponent ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)) ∧
      topologicalKrullDim G₀ = n ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      (L.IsCommutative → L₀.IsCommutative) ∧
      ∃ S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f), S.Finite ∧
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
          ∃ s ∈ S, ∃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (i ≫ f),
            x = L.mul (𝟙 (Spec (CommRingCat.of k))) s
              (NeronModelInfra.schemeHomOverComp a (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)) := by

  haveI : Smooth (fr f) := smooth_fr L
  haveI : QuasiCompact (fr f) := inferInstance

  obtain ⟨G₀, i₀, L₀, hoi, hci, hirr, hgi, -, hrange, -, hhom, hcomm, S, hSfin, hS⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
      k (lawr L)
  have e : i₀ ≫ ιr G ≫ f = (i₀ ≫ ιr G) ≫ f := (Category.assoc _ _ _).symm
  haveI : Smooth ((i₀ ≫ ιr G) ≫ f) := by rw [Category.assoc]; infer_instance
  obtain ⟨n, hn⟩ :=
    AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace ((i₀ ≫ ιr G) ≫ f)
  haveI : Nonempty G₀ := inferInstance
  refine ⟨G₀, i₀ ≫ ιr G, castLaw e L₀, n, inferInstance, hirr, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact hgi
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (isHomeomorph_ιr G).isOpenMap _ i₀.isOpenEmbedding.isOpen_range
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange,
      image_connectedComponent_of_isHomeomorph (isHomeomorph_ιr G)]
    congr 1
    have h1 : ((lawr L).one (𝟙 _)).1 ≫ ιr G = (L.one (𝟙 _)).1 :=
      congrArg Subtype.val (toG_lawr_one L (𝟙 _))
    rw [← h1]
    rfl
  · haveI := hn
    exact le_antisymm
      (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le ((i₀ ≫ ιr G) ≫ f) n)
      (AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim ((i₀ ≫ ιr G) ≫ f) n)
  · intro T t x y
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, castLaw_mul_val]
    set x' : SchemeHomOver t (i₀ ≫ ιr G ≫ f) := ⟨x.1, by rw [e]; exact x.2⟩ with hx'
    set y' : SchemeHomOver t (i₀ ≫ ιr G ≫ f) := ⟨y.1, by rw [e]; exact y.2⟩ with hy'
    have h1 := congrArg Subtype.val (hhom t x' y')
    have h2 := congrArg Subtype.val (hom_ιr L t
      (NeronModelInfra.schemeHomOverComp x' (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ fr f) (fr f)))
      (NeronModelInfra.schemeHomOverComp y' (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ fr f) (fr f))))
    simp only [NeronModelInfra.schemeHomOverComp_coe] at h1 h2
    rw [← Category.assoc, h1, h2]
    congr 2
  · intro hc
    exact isCommutative_castLaw e L₀ (hcomm (isCommutative_lawr L hc))
  · refine ⟨toG '' S, hSfin.image _, fun x => ?_⟩
    obtain ⟨x', hx'⟩ := toG_surjective (f := f) x
    obtain ⟨s, hs, a, ha⟩ := hS x'
    refine ⟨toG s, Set.mem_image_of_mem _ hs, ⟨a.1, by rw [← e]; exact a.2⟩, ?_⟩
    rw [← hx', ha, toG_lawr_mul]
    congr 1

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField (solution)
