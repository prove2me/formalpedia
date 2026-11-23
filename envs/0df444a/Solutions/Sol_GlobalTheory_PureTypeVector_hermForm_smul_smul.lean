-- Prove2me | solution 1 for GlobalTheory.PureTypeVector.hermForm_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:07.407801+00:00
-- url     : https://prove2.me/submissions/5b373719-3e5d-415a-8f8d-53fa30c2289c

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
theorem _root_.solution {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : ℂ) (u v : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • u) (w • v) = z * starRingEnd ℂ w * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm u v := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def]
  ring
end _root_.GlobalTheory.PureTypeVector
end GlobalTheory.PureTypeVector
