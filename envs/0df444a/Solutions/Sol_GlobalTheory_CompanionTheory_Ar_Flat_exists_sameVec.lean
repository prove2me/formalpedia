-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.exists_sameVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:31.599832+00:00
-- url     : https://prove2.me/submissions/2c2fdf88-fe00-4d4e-9da2-30fd689c095b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsConstMul
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {Xo : Moduli D l} {c : Coeff l}
variable {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.CompanionTheory.Ar.Flat
theorem _root_.solution (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v : epsAt (under y) ⟶ Xo.univ.t.G) : ∃ v', SameVec Y y v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv : v.left ≫ Xo.univ.t.G.hom = (spMap (algebraMap F (DualNumber F)) ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact Over.w v
  refine ⟨Over.homMk (hp.lift _ _ hv ≫ Y.m.φ) ?_, hp.lift _ _ hv, hp.lift_snd _ _ _, hp.lift_fst _ _ _, rfl⟩
  have : (hp.lift _ _ hv ≫ Y.m.φ) ≫ Y.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y ≫ Y.j := by
    rw [Category.assoc, hq.w, ← Category.assoc, hp.lift_snd, Category.assoc]
  exact this
end GlobalTheory.CompanionTheory.Ar.Flat
