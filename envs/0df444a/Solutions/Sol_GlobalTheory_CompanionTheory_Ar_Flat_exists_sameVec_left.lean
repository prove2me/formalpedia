-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.exists_sameVec_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:38.208917+00:00
-- url     : https://prove2.me/submissions/47c33505-6043-4364-b209-dd7affbf00e1

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
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : ∃ v, SameVec Y y v v' := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  have hv : v'.left ≫ Y.t.G.hom = (spMap (algebraMap F (DualNumber F)) ≫ y) ≫ Y.j := by
    rw [Category.assoc]; exact Over.w v'
  refine ⟨Over.homMk (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ?_, hq.lift _ _ hv, hq.lift_snd _ _ _, rfl,
    hq.lift_fst _ _ _⟩
  have : (hq.lift _ _ hv ≫ Y.m0.toSABMap.φ) ≫ Xo.univ.t.G.hom =
      spMap (algebraMap F (DualNumber F)) ≫ y ≫ pullback.fst _ _ := by
    rw [Category.assoc, hp.w, ← Category.assoc, hq.lift_snd, Category.assoc]
  exact this
end GlobalTheory.CompanionTheory.Ar.Flat
