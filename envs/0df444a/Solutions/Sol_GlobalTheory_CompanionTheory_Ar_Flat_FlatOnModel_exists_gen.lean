-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.FlatOnModel.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:53.228279+00:00
-- url     : https://prove2.me/submissions/a8372ff1-6e1c-4e90-9000-30ca089b7452

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
namespace FlatOnModel
theorem _root_.solution {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧
      Represents Y U τ Z.M a b φ := h.2
end FlatOnModel
end GlobalTheory.CompanionTheory.Ar.Flat
