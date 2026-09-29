-- Prove2me | solution 1 for ModularCurve.XOneP.finitePart_toricPart_zero_mem_add_mem_neg_mem_sub_mem_points_valuationSubring_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d1d50a22-d9ae-59f8-9fc5-c195ec39186c

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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_finitePart_toricPart_zero_mem_add_mem_neg_mem_sub_mem_points_valuationSubring_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

universe u v w x

namespace TorAddX1

open GoodReductionJacobian

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem eq_one_of_mul_self {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f)
    (h : G.mul t a a = a) : a = G.one t :=
  calc a = G.mul t (G.one t) a := (G.one_mul t a).symm
    _ = G.mul t (G.mul t (G.inv t a) a) a := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t a) (G.mul t a a) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t a) a := by rw [h]
    _ = G.one t := G.inv_mul_cancel t a

theorem eq_inv_of_mul_eq_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t f)
    (h : G.mul t a b = G.one t) : b = G.inv t a :=
  calc b = G.mul t (G.one t) b := (G.one_mul t b).symm
    _ = G.mul t (G.mul t (G.inv t a) a) b := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t a) (G.mul t a b) := G.mul_assoc t _ _ _
    _ = G.mul t (G.inv t a) (G.one t) := by rw [h]
    _ = G.inv t a := G.mul_one t _

variable {R' : Type u} [CommRing R'] {X' : Scheme.{u}} {f' : X' ⟶ Spec (CommRingCat.of R')} (G' : RelativeGroupLaw R' f')

theorem map_one {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R'))
    (Φ : SchemeHomOver t f → SchemeHomOver t' f')
    (hΦ : ∀ u v, Φ (G.mul t u v) = G'.mul t' (Φ u) (Φ v)) : Φ (G.one t) = G'.one t' := by
  apply eq_one_of_mul_self G' t'
  rw [← hΦ, G.one_mul]

theorem map_inv {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R'))
    (Φ : SchemeHomOver t f → SchemeHomOver t' f')
    (hΦ : ∀ u v, Φ (G.mul t u v) = G'.mul t' (Φ u) (Φ v)) (u : SchemeHomOver t f) :
    Φ (G.inv t u) = G'.inv t' (Φ u) := by
  apply eq_inv_of_mul_eq_one G' t'
  rw [← hΦ, G.mul_inv_cancel, map_one G G' t t' Φ hΦ]

theorem comp_inv {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t a) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) :=
  map_inv G G t t' (GoodReductionJacobian.schemeHomOverComp ψ hψ) (G.mul_natural t t' ψ hψ) a

end TorAddX1

namespace TorAddX1

theorem main
    {A : Type u} [CommRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c)
    (D : RelativePic0Designation A c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (k : Type u) [CommRing k] [Algebra A k]
    (hreps : RepresentsRelSubPic (baseChange A c k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A c k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR c ε k
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    {J0s : Type v} [AddCommGroup J0s] {W : Type w} [AddCommGroup W] (proj : J0s →+ W)
    (pts : J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (hadd : ∀ a b : J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    {V : Type x} [AddCommGroup V] (Q : Type u) [CommRing Q] [Algebra A Q]
    (gpts : V ≃ SchemeHomOver (specMap A Q) D.toBase)
    (hgadd : ∀ x y : V, gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h).mul _ (gpts x) (gpts y))
    (O : Type u) [CommRing O] (ι : O →+* Q) (ρ : A →+* O) (hρ : ι.comp ρ = algebraMap A Q)
    (πk : O →+* k) (hAlgk : algebraMap A k = πk.comp ρ) :
    (∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (0 : V)).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1) ∧
    (∀ (x x' : V) (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
      (gpts x).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1 → (gpts x').1 = Spec.map (CommRingCat.ofHom ι) ≫ z'.1 →
        ∃ z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (x + x')).1 = Spec.map (CommRingCat.ofHom ι) ≫ z''.1) ∧
    (∀ (x : V) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
      (gpts x).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1 → ∃ z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (-x)).1 = Spec.map (CommRingCat.ofHom ι) ≫ z'.1) ∧
    (∀ (x x' : V) (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
      (gpts x).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1 → (gpts x').1 = Spec.map (CommRingCat.ofHom ι) ≫ z'.1 →
        ∃ z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (x - x')).1 = Spec.map (CommRingCat.ofHom ι) ≫ z''.1) ∧
    (∃ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : J0s),
      (gpts (0 : V)).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1 ∧
        (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 ∧ proj y = 0) ∧
    (∀ (x x' : V) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : J0s) (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y' : J0s),
      (gpts x).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → proj y = 0 →
      (gpts x').1 = Spec.map (CommRingCat.ofHom ι) ≫ z'.1 → (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z'.1 → proj y' = 0 →
        ∃ (z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y'' : J0s),
          (gpts (x + x')).1 = Spec.map (CommRingCat.ofHom ι) ≫ z''.1 ∧ (pts y'').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z''.1 ∧ proj y'' = 0) ∧
    (∀ (x : V) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : J0s),
      (gpts x).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → proj y = 0 →
        ∃ (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y' : J0s),
          (gpts (-x)).1 = Spec.map (CommRingCat.ofHom ι) ≫ z'.1 ∧ (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z'.1 ∧ proj y' = 0) ∧
    (∀ (x x' : V) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : J0s) (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y' : J0s),
      (gpts x).1 = Spec.map (CommRingCat.ofHom ι) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → proj y = 0 →
      (gpts x').1 = Spec.map (CommRingCat.ofHom ι) ≫ z'.1 → (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z'.1 → proj y' = 0 →
        ∃ (z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y'' : J0s),
          (gpts (x - x')).1 = Spec.map (CommRingCat.ofHom ι) ≫ z''.1 ∧ (pts y'').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z''.1 ∧ proj y'' = 0) := by
  classical

  obtain ⟨GD, hGD⟩ : ∃ GD : RelativeGroupLaw A D.toBase,
      GD = RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) h := ⟨_, rfl⟩
  obtain ⟨Gk, hGk⟩ : ∃ Gk : RelativeGroupLaw k (D.baseChange k).toBase,
      Gk = RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps := ⟨_, rfl⟩
  have hgadd' : ∀ x y : V, gpts (x + y) = GD.mul _ (gpts x) (gpts y) := fun x y => by rw [hGD]; exact hgadd x y

  have hψ : (Spec.map (CommRingCat.ofHom ι)) ≫ (Spec.map (CommRingCat.ofHom ρ)) = specMap A Q := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have hφ : (Spec.map (CommRingCat.ofHom πk)) ≫ (Spec.map (CommRingCat.ofHom ρ)) = 𝟙 _ ≫ specMap A k := by
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]

  have hg0 : gpts 0 = GD.one (specMap A Q) := by
    apply TorAddX1.eq_one_of_mul_self GD
    rw [← hgadd', add_zero]
  have hgneg : ∀ x : V, gpts (-x) = GD.inv (specMap A Q) (gpts x) := by
    intro x
    apply TorAddX1.eq_inv_of_mul_eq_one GD
    rw [← hgadd', add_neg_cancel, hg0]
  have hext : ∀ (x : V) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase), (gpts x).1 = (Spec.map (CommRingCat.ofHom ι)) ≫ z.1 →
      gpts x = GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom ι)) hψ z := fun x z h => Subtype.ext h

  have hF0 : (gpts (0 : V)).1 = (Spec.map (CommRingCat.ofHom ι)) ≫ (GD.one (Spec.map (CommRingCat.ofHom ρ))).1 := by
    rw [hg0, ← GD.one_natural (Spec.map (CommRingCat.ofHom ρ)) _ (Spec.map (CommRingCat.ofHom ι)) hψ]
    rfl
  have hFadd : ∀ (x x' : V) (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
      (gpts x).1 = (Spec.map (CommRingCat.ofHom ι)) ≫ z.1 → (gpts x').1 = (Spec.map (CommRingCat.ofHom ι)) ≫ z'.1 →
        (gpts (x + x')).1 = (Spec.map (CommRingCat.ofHom ι)) ≫ (GD.mul (Spec.map (CommRingCat.ofHom ρ)) z z').1 := by
    intro x x' z z' hz hz'
    rw [hgadd', hext x z hz, hext x' z' hz', ← GD.mul_natural (Spec.map (CommRingCat.ofHom ρ)) _ (Spec.map (CommRingCat.ofHom ι)) hψ]
    rfl
  have hFneg : ∀ (x : V) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase), (gpts x).1 = (Spec.map (CommRingCat.ofHom ι)) ≫ z.1 →
      (gpts (-x)).1 = (Spec.map (CommRingCat.ofHom ι)) ≫ (GD.inv (Spec.map (CommRingCat.ofHom ρ)) z).1 := by
    intro x z hz
    rw [hgneg, hext x z hz, ← TorAddX1.comp_inv GD (Spec.map (CommRingCat.ofHom ρ)) _ (Spec.map (CommRingCat.ofHom ι)) hψ]
    rfl

  let Φ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k)) ≫ specMap A k) D.toBase := fun u =>
    ⟨u.1 ≫ pullback.fst D.toBase (specMap A k), by
      rw [Category.assoc, pullback.condition, ← Category.assoc, u.2]⟩
  have hΦmul : ∀ u v, Φ (Gk.mul _ u v) = GD.mul _ (Φ u) (Φ v) := by
    intro u v
    apply Subtype.ext
    show (Gk.mul _ u v).1 ≫ pullback.fst D.toBase (specMap A k) = (GD.mul _ (Φ u) (Φ v)).1
    rw [hGk, hGD]
    exact AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat A c ε D h k hreps hPk (𝟙 _) u v
      (Φ u) (Φ v) rfl rfl
  have hΦone : Φ (Gk.one _) = GD.one _ := TorAddX1.map_one Gk GD _ _ Φ hΦmul
  have hΦinv : ∀ u, Φ (Gk.inv _ u) = GD.inv _ (Φ u) := TorAddX1.map_inv Gk GD _ _ Φ hΦmul

  have hpadd : ∀ a b : J0s, pts (a + b) = Gk.mul _ (pts a) (pts b) := by
    intro a b
    rw [hGk]
    apply hreps.ext_of_iso
    letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut _ _) hreps
    obtain ⟨e₁⟩ := hadd a b
    obtain ⟨e₂⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hreps
      (T := Over.mk (𝟙 _)) (schemeHomOverToOverHom (pts a)) (schemeHomOverToOverHom (pts b))
    exact ⟨e₁ ≪≫ e₂.symm⟩
  have hp0 : pts 0 = Gk.one _ := by
    apply TorAddX1.eq_one_of_mul_self Gk
    rw [← hpadd, add_zero]
  have hpneg : ∀ y : J0s, pts (-y) = Gk.inv _ (pts y) := by
    intro y
    apply TorAddX1.eq_inv_of_mul_eq_one Gk
    rw [← hpadd, add_neg_cancel, hp0]
  have hred : ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : J0s),
      (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = (Spec.map (CommRingCat.ofHom πk)) ≫ z.1 →
        Φ (pts y) = GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom πk)) hφ z := fun z y h => Subtype.ext h

  have hT0 : (pts (0 : J0s)).1 ≫ pullback.fst D.toBase (specMap A k) = (Spec.map (CommRingCat.ofHom πk)) ≫ (GD.one (Spec.map (CommRingCat.ofHom ρ))).1 := by
    have h1 : (Φ (pts 0)).1 = (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom πk)) hφ (GD.one (Spec.map (CommRingCat.ofHom ρ)))).1 := by
      rw [hp0, hΦone, GD.one_natural]
    exact h1
  have hTadd : ∀ (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y y' : J0s),
      (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = (Spec.map (CommRingCat.ofHom πk)) ≫ z.1 →
      (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = (Spec.map (CommRingCat.ofHom πk)) ≫ z'.1 →
        (pts (y + y')).1 ≫ pullback.fst D.toBase (specMap A k) = (Spec.map (CommRingCat.ofHom πk)) ≫ (GD.mul (Spec.map (CommRingCat.ofHom ρ)) z z').1 := by
    intro z z' y y' hy hy'
    have h1 : (Φ (pts (y + y'))).1 = (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom πk)) hφ (GD.mul (Spec.map (CommRingCat.ofHom ρ)) z z')).1 := by
      rw [hpadd, hΦmul, hred z y hy, hred z' y' hy', GD.mul_natural]
    exact h1
  have hTneg : ∀ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : J0s),
      (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = (Spec.map (CommRingCat.ofHom πk)) ≫ z.1 →
        (pts (-y)).1 ≫ pullback.fst D.toBase (specMap A k) = (Spec.map (CommRingCat.ofHom πk)) ≫ (GD.inv (Spec.map (CommRingCat.ofHom ρ)) z).1 := by
    intro z y hy
    have h1 : (Φ (pts (-y))).1 = (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom πk)) hφ (GD.inv (Spec.map (CommRingCat.ofHom ρ)) z)).1 := by
      rw [hpneg, hΦinv, hred z y hy, TorAddX1.comp_inv]
    exact h1
  refine ⟨⟨GD.one _, hF0⟩, ?_, ?_, ?_, ⟨GD.one _, 0, hF0, hT0, map_zero _⟩, ?_, ?_, ?_⟩
  · intro x x' z z' hz hz'
    exact ⟨GD.mul _ z z', hFadd x x' z z' hz hz'⟩
  · intro x z hz
    exact ⟨GD.inv _ z, hFneg x z hz⟩
  · intro x x' z z' hz hz'
    refine ⟨GD.mul _ z (GD.inv _ z'), ?_⟩
    rw [sub_eq_add_neg]
    exact hFadd x (-x') z _ hz (hFneg x' z' hz')
  · intro x x' z y z' y' hz hy hπy hz' hy' hπy'
    refine ⟨GD.mul _ z z', y + y', hFadd x x' z z' hz hz', hTadd z z' y y' hy hy', ?_⟩
    rw [map_add, hπy, hπy', add_zero]
  · intro x z y hz hy hπy
    refine ⟨GD.inv _ z, -y, hFneg x z hz, hTneg z y hy, ?_⟩
    rw [map_neg, hπy, neg_zero]
  · intro x x' z y z' y' hz hy hπy hz' hy' hπy'
    refine ⟨GD.mul _ z (GD.inv _ z'), y + -y', ?_, hTadd z _ y (-y') hy (hTneg z' y' hy'), ?_⟩
    · rw [sub_eq_add_neg]
      exact hFadd x (-x') z _ hz (hFneg x' z' hz')
    · rw [map_add, map_neg, hπy, hπy', neg_zero, add_zero]

end TorAddX1

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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    (Mdl₂ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₂ : Mdl₂.C ≅ C₂)
    (he₂ : e₂.hom ≫ c₂ = Mdl₂.toBase)

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))

    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk) :
    (∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (0 : ModularCurve.JOne (M * p))).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1) ∧
    (∀ (x x' : ModularCurve.JOne (M * p)) (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
      (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → (gpts x').1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 →
        ∃ z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (x + x')).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z''.1) ∧
    (∀ (x : ModularCurve.JOne (M * p)) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
      (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → ∃ z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (-x)).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1) ∧
    (∀ (x x' : ModularCurve.JOne (M * p)) (z z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
      (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → (gpts x').1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 →
        ∃ z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase, (gpts (x - x')).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z''.1) ∧
    (∃ (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s),
      (gpts (0 : ModularCurve.JOne (M * p))).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 ∧
        (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 ∧ G.proj y = 0) ∧
    (∀ (x x' : ModularCurve.JOne (M * p)) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s) (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y' : G.J0s),
      (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → G.proj y = 0 →
      (gpts x').1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 → (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z'.1 → G.proj y' = 0 →
        ∃ (z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y'' : G.J0s),
          (gpts (x + x')).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z''.1 ∧ (pts y'').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z''.1 ∧ G.proj y'' = 0) ∧
    (∀ (x : ModularCurve.JOne (M * p)) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s),
      (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → G.proj y = 0 →
        ∃ (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y' : G.J0s),
          (gpts (-x)).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 ∧ (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z'.1 ∧ G.proj y' = 0) ∧
    (∀ (x x' : ModularCurve.JOne (M * p)) (z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y : G.J0s) (z' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y' : G.J0s),
      (gpts x).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z.1 → (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z.1 → G.proj y = 0 →
      (gpts x').1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z'.1 → (pts y').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z'.1 → G.proj y' = 0 →
        ∃ (z'' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase) (y'' : G.J0s),
          (gpts (x - x')).1 = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ z''.1 ∧ (pts y'').1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ z''.1 ∧ G.proj y'' = 0) :=
  TorAddX1.main (ModularCurve.TwoChart.modelTo A (↥K) j) ε D hrep.some k hreps hPk G.proj pts hadd
    (AlgebraicClosure ℚ) gpts hgadd (↥Pl) Pl.subtype ρ hρ πk hAlgk

#print axioms solution

end S_ModularCurve_XOneP_finitePart_toricPart_zero_mem_add_mem_neg_mem_sub_mem_points_valuationSubring_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_finitePart_toricPart_zero_mem_add_mem_neg_mem_sub_mem_points_valuationSubring_twoChartModel_x1_mul (solution)
