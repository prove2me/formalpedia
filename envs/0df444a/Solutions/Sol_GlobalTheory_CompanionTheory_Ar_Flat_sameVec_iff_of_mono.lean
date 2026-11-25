-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.sameVec_iff_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:32:00.201747+00:00
-- url     : https://prove2.me/submissions/041d3377-36c7-4c8c-b036-c08de079d215

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
theorem _root_.solution (Y : Model Xo c β) [Mono Y.j] {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) :
    SameVec Y y v v' ↔
      ∃ u : Sp (DualNumber F) ⟶ Y.oF.t.G.left, u ≫ Y.m0.toSABMap.φ = v.left ∧ u ≫ Y.m.φ = v'.left := by
  have hq : IsPullback Y.m.φ Y.oF.t.G.hom Y.t.G.hom Y.j := Y.m.cart.1
  refine ⟨fun ⟨u, _, a, b⟩ => ⟨u, a, b⟩, fun ⟨u, a, b⟩ => ⟨u, ?_, a, b⟩⟩
  rw [← cancel_mono Y.j, Category.assoc, ← hq.w, ← Category.assoc, b, Category.assoc]
  exact Over.w v'
end GlobalTheory.CompanionTheory.Ar.Flat
