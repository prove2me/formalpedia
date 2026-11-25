-- Prove2me | solution 1 for GlobalTheory.ChF.qRel_one_iff_exists_iRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:57.681803+00:00
-- url     : https://prove2.me/submissions/2da346f2-b523-4cc3-9026-744ad60da54c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThickeningQuotientImageOneIffExistsTorusImage
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_a1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
namespace GlobalTheory.ChF
private theorem one_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (h : t ≫ f = r) :
    (1 : Over.mk t ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk r ⟶ G).left := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (𝟙_ (Over S)) :=
    toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f)
  have h1 : (1 : Over.mk t ⟶ (Over.pullback f).obj G) = z ≫ (Over.pullback f).map η[G] := by
    rw [Hom.one_def, Functor.obj.η_def, ← Category.assoc]
  have h2 : z.left ≫ pullback.fst (𝟙_ (Over S)).hom f = (toUnit (Over.mk r)).left := by
    have a1 : pullback.fst (𝟙_ (Over S)).hom f ≫ (𝟙_ (Over S)).hom = pullback.snd _ f ≫ f := pullback.condition
    have a2 : z.left ≫ pullback.snd (𝟙_ (Over S)).hom f = t := Over.w z
    have a3 : (toUnit (Over.mk r)).left ≫ (𝟙_ (Over S)).hom = r := Over.w _
    have : Mono (𝟙_ (Over S)).hom := inferInstanceAs (Mono (𝟙 S))
    rw [← cancel_mono (𝟙_ (Over S)).hom, a3, Category.assoc, a1, ← Category.assoc, a2, h]
  rw [h1, Over.comp_left, Category.assoc, A, ← Category.assoc, h2, Hom.one_def, Over.comp_left]
private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance
end GlobalTheory.ChF
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ z, QRel c S z 1 ↔ ∃ χ, IRel c S χ z := by
  intro R _ _ I D k G _ _ c S _ _ hS z
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst D.P.A.hom (Out.thick R I k)) := inferInstance
  let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
  have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hw : ∀ (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
      w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
    intro w h
    rw [← cancel_mono (Out.thick R I k), ht]
    have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
      (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
    rw [Category.assoc, h1, ← Category.assoc, h]
    exact Over.w z
  have h1 : (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left ≫ pullback.fst D.P.A.hom (Out.thick R I k) =
      (1 : sp (R₀ := R) S ⟶ D.P.A).left := one_left_fst D.P.A (Out.thick R I k) ht
  constructor
  · rintro ⟨w, a, b⟩
    let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw w a)
    have hx : x ≫ c.q = toUnit _ ≫ η[Out.thickObj R I k D.P.A] := by
      apply Over.OverMorphism.ext
      refine (cancel_mono (pullback.fst D.P.A.hom (Out.thick R I k))).1 ?_
      exact ((Category.assoc _ _ _).trans b).trans h1.symm
    let u := c.isKernel.lift x (toUnit _) hx
    have hu : u ≫ c.i = x := c.isKernel.lift_fst _ _ _
    refine ⟨(Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom).comp
      (splitTorusPointsEquiv _ D.X (Over.mk t) u), u.left, fun χ => ?_, ?_⟩
    · exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (splitTorusPointsEquiv_val _ D.X (Over.mk t) u χ)).symm
    · have e : u.left ≫ c.i.left = w := congrArg (·.left) hu
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans a
  · rintro ⟨χ, w, -, a⟩
    have a' : (w ≫ c.i.left) ≫ (Out.fstG I k G).left = z.left := (Category.assoc _ _ _).trans a
    refine ⟨w ≫ c.i.left, a', ?_⟩
    let u : Over.mk t ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w (by
      have := hw _ a'
      rw [Category.assoc, Over.w c.i] at this
      exact this)
    have hu : u ≫ c.i ≫ c.q = 1 := by
      rw [c.isKernel.w, Hom.one_def, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have e : (w ≫ c.i.left) ≫ c.q.left = (1 : Over.mk t ⟶ Out.thickObj R I k D.P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (·.left) hu)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e)).trans h1
end GlobalTheory.ChF
