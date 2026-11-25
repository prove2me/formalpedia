-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth.IsChartAt.unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:58.118704+00:00
-- url     : https://prove2.me/submissions/4a9d4c50-93ec-45c8-a779-140daa97f5a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
namespace IsChartAt
theorem _root_.solution {Y : Model Xo c β} (hY : Y.N3) {x : Y.X} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {ξ : Sp R ⟶ Y.X} (h : IsChartAt Y x R ξ) :
    ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G) := by
  obtain ⟨h0, h1, h2, h3, -, h5, t, m, S, hS⟩ := h
  exact ⟨t, m, hY R h1 h2 h3 ξ t m h5 ⟨S, hS⟩⟩
end IsChartAt
end GlobalTheory.IndefiniteRowSideFullHecke.CoveringAbelianLocusSmooth
