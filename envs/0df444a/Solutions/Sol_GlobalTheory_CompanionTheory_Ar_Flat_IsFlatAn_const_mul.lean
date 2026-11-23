-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.IsFlatAn.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:52.466456+00:00
-- url     : https://prove2.me/submissions/d2d219f4-849f-489a-9737-b3a6a93c17a9

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
namespace IsFlatAn
theorem _root_.solution {U : Set (Xo.XF c)} {τ τ' : E →+* ℂ} {σ : c.F →+* ℂ} {Φ : CFn Xo c} {σK : KA l →+* ℂ}
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo σK ty} {i : Fin FU.n}
    {e : Fin D.p ⊕ Fin D.q → (FU.Di i).La} {ρ : ℂ} (h : IsFlatAn U τ τ' σ Φ FU i e ρ) (k : ℂ) :
    IsFlatAn U τ τ' σ (fun y v w => k * Φ y v w) FU i e (k * ρ) := by
  intro P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8
  show k * Φ y v w * _ = _
  rw [_root_.mul_assoc, h P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8]
end IsFlatAn
end GlobalTheory.CompanionTheory.Ar.Flat
