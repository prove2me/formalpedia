-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase.AbLocusSmooth.smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:40.88067+00:00
-- url     : https://prove2.me/submissions/edeac3af-25ce-40e8-a64c-ede47ce9ff57

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
namespace AbLocusSmooth
theorem _root_.solution {Y : Model Xo c β} (h : AbLocusSmooth Y) (U : Y.X.Opens)
    (hU : (U : Set Y.X) = abLocus Y.t.G) : SmoothOfRelativeDimension D.dim (U.ι ≫ Y.s) := by
  obtain ⟨U', hU', hs⟩ := h
  obtain rfl : U = U' := SetLike.coe_injective (hU.trans hU'.symm)
  exact hs
end AbLocusSmooth
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBase
