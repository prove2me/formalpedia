-- Prove2me | solution 1 for GlobalTheory.PureTypeVector.hermForm_self_im
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:07.142503+00:00
-- url     : https://prove2.me/submissions/a2436fb9-f322-4b38-8741-c4db7793fcbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_PureTypeVectorSpansQuadraticLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.PureTypeVector
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open scoped CategoryTheory.Obj
namespace GlobalTheory.PureTypeVector
namespace _root_.GlobalTheory.PureTypeVector
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (v : Fin g → ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm v v).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
  have := key (star v)
  rw [star_star] at this
  exact this
end _root_.GlobalTheory.PureTypeVector
end GlobalTheory.PureTypeVector
