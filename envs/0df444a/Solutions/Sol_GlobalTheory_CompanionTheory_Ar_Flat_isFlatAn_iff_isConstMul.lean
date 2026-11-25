-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.isFlatAn_iff_isConstMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:45.554948+00:00
-- url     : https://prove2.me/submissions/279f3778-1472-4710-a26d-6c271fd38a7e

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
attribute [instance] CptOver.field CptOver.acg CptOver.mod
namespace GlobalTheory.CompanionTheory.Ar.Flat
theorem _root_.solution (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) :
    IsFlatAn U τ τ (algebraMap c.F ℂ) (φ ℂ) FU i e ρ ↔ IsConstMul U τ φ FU i e ρ := Iff.rfl
end GlobalTheory.CompanionTheory.Ar.Flat
