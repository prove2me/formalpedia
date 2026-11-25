-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.ExtendsUnitAt.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:01.977199+00:00
-- url     : https://prove2.me/submissions/dd11a0cd-7ad8-4b4d-b6c4-84a30d120bc1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsConstMul
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_IsFlatAn_const_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_IsUnitAn_const_mul

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
namespace ExtendsUnitAt
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} {s : X ⟶ Sp K} {σ : K →+* ℂ}
    {ξ : Sp Ω ⟶ X} {W : X.Opens} {F : (Sp ℂ ⟶ X) → ℂ} {t : Ω} {x : Sp ℂ ⟶ X}
    (h : ExtendsUnitAt s σ ξ W F t x) {k : ℂ} (hk : k ≠ 0) : ExtendsUnitAt s σ ξ W (fun y => k * F y) t x := by
  intro m B y h1 h2 h3 b₀ h4 h5
  obtain ⟨ε, g, hε, hd, hg, H⟩ := h m B y h1 h2 h3 b₀ h4 h5
  refine ⟨ε, fun b => k * g b, hε, hd.const_mul k, mul_ne_zero hk hg, fun b hb hW r hr => ?_⟩
  show k * F (y b) = k * g b * r
  rw [H b hb hW r hr, _root_.mul_assoc]
end ExtendsUnitAt
end GlobalTheory.CompanionTheory.Ar.Flat
