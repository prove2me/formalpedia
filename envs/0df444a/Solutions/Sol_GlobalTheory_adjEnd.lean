-- Prove2me | solution 1 for GlobalTheory.adjEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:41:12.367551+00:00
-- url     : https://prove2.me/submissions/ba873ed7-cbe3-4998-bbb5-7f6454e33970

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GrpPullbackSquareProductLift
import Theorems.Thm_GlobalTheory_adjPoints
import Theorems.Thm_GlobalTheory_adjBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] (B : BX R₀)
    (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y)
    (hn : ∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)
    (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] (φ : G'.left ⟶ G.left)
    (gp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ)
    (f : G' ⟶ G') [IsMonHom f] : ∃ a : OEnd B O, ∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (a.f s x)).left := by
  choose E hE using fun (R : LAlg R₀) (s : LHom O R) => adjPoints gp _ _ (adjBase s)
  choose F hF using fun (R : LAlg R₀) (s : LHom O R) (x : B.G R) => (hb R).2 (E R s ((E R s).symm (e R x) ≫ f))
  have spec : ∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (F R s x)).left := fun {R} s x x' h => by
    have : e R x = E R s x' := Over.OverMorphism.ext (h.symm.trans (hE R s x').symm)
    rw [hF, this, MulEquiv.symm_apply_apply, hE]
  refine ⟨⟨fun {R} s => AddMonoidHom.mk' (F R s) fun x y => (hb R).1 ?_, fun {R S} s g x => (hb S).1 ?_⟩, spec⟩
  · rw [hm, hF, hF, hF, hm]
    exact (congrArg (fun q => E R s (q ≫ f)) (map_mul (E R s).symm _ _)).trans
      ((congrArg (E R s) (MonObj.mul_comp _ _ _)).trans (map_mul (E R s) _ _))
  · let x' := (E R s).symm (e R x)
    have hx : x'.left ≫ φ = (e R x).left :=
      (hE R s x').symm.trans (congrArg (fun q => q.left) ((E R s).apply_symm_apply _))
    let U : Over.mk (Spec.map (CommRingCat.ofHom (g.comp s).1.toRingHom)) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) :=
      Over.homMk (Spec.map (CommRingCat.ofHom g.1.toRingHom)) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]; rfl)
    have h₁ := spec (g.comp s) (B.map g x) (U ≫ x') (by
      rw [hn]
      exact (Category.assoc _ _ _).trans (congrArg (U.left ≫ ·) hx))
    refine Over.OverMorphism.ext (h₁.symm.trans ?_)
    show _ = (e S (B.map g (F R s x))).left
    rw [hn, Category.assoc]
    exact (Category.assoc _ _ _).trans (congrArg (U.left ≫ ·) (spec s x x' hx))
end GlobalTheory
