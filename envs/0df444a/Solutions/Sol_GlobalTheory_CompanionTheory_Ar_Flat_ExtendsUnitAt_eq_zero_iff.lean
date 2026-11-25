-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.ExtendsUnitAt.eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:04.999063+00:00
-- url     : https://prove2.me/submissions/35410556-add1-4e97-b77c-d95cb91323af

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
namespace ExtendsUnitAt
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} {s : X ⟶ Sp K} {σ : K →+* ℂ}
    {ξ : Sp Ω ⟶ X} {W : X.Opens} {F : (Sp ℂ ⟶ X) → ℂ} {t : Ω} {x : Sp ℂ ⟶ X} (h : ExtendsUnitAt s σ ξ W F t x)
    (hx : x ≫ s = spMap σ) (hW : ⊤ ≤ x ⁻¹ᵁ W) {r : ℂ} (hr : ValAt ξ x t r) : F x = 0 ↔ r = 0 := by
  have hol : IsHolTo (Set.univ : Set (Fin 0 → ℂ)) (fun _ => x) := fun U f =>
    ⟨isOpen_discrete _, differentiableOn_const _⟩
  obtain ⟨ε, g, hε, -, hg, H⟩ := h 0 Set.univ (fun _ => x) isOpen_univ hol (fun _ _ => hx) 0 trivial rfl
  rw [H 0 ⟨trivial, Metric.mem_ball_self hε⟩ hW r hr]
  exact ⟨fun h0 => (mul_eq_zero.mp h0).resolve_left hg, fun h0 => by rw [h0, mul_zero]⟩
end ExtendsUnitAt
end GlobalTheory.CompanionTheory.Ar.Flat
