-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.SameVec.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:45:59.550046+00:00
-- url     : https://prove2.me/submissions/dbed203c-7c8e-4e7c-87b6-3e59f9c54b8f

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
namespace SameVec
theorem _root_.solution {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    {v : epsAt (under y) ⟶ Xo.univ.t.G} {v₁ v₂ : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y v v₁) (h₂ : SameVec Y y v v₂) : v₁ = v₂ := by
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  obtain ⟨u₁, a₁, b₁, c₁⟩ := h₁
  obtain ⟨u₂, a₂, b₂, c₂⟩ := h₂
  have : u₁ = u₂ := hp.hom_ext (b₁.trans b₂.symm) (a₁.trans a₂.symm)
  ext1
  rw [← c₁, ← c₂, this]
end SameVec
end GlobalTheory.CompanionTheory.Ar.Flat
