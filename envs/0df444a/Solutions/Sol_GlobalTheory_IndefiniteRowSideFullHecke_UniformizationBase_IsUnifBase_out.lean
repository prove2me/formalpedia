-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase.IsUnifBase.out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:04.771043+00:00
-- url     : https://prove2.me/submissions/7d812802-9e5e-4527-8098-9b907bf317a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
namespace IsUnifBase
theorem _root_.solution {Y : Model Xo c β} (h3 : Y.N3) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsUnifBase Y R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by
  obtain ⟨h0, hn, hi, hc, hU, t, m, S, hS⟩ := h
  exact ⟨t, m, h3 R hn hi hc ξ t m hU ⟨S, hS⟩⟩
end IsUnifBase
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
