-- Prove2me | solution 1 for GlobalTheory.PullHermitian.wchart_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:24.05012+00:00
-- url     : https://prove2.me/submissions/8ec70dce-2d88-437f-a7b1-eec1e6ed4d86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow

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
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.PullHermitian
theorem _root_.solution {Y : Scheme.{0}} (L : LB Y) (φ : X ⟶ Y) (j : L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ L.wchart (K := PUnit) (fun _ => φ) (fun _ => j) :=
  fun _ hp => Set.mem_iInter.2 fun _ => h hp
end GlobalTheory.PullHermitian
