-- Prove2me | solution 1 for GlobalTheory.PullHermitian.idx_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:56.528055+00:00
-- url     : https://prove2.me/submissions/47752a17-ba93-4c01-8469-b4d500aed387

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Theorems.Thm_GlobalTheory_PullHermitian_wchart_of

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
theorem _root_.solution {Y : Scheme.{0}} {L : LB X} {L' : LB Y} (f : X ⟶ Y) (m n : ℕ) (i : L.ι) (j : L'.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (x ≫ f) ⁻¹ᵁ L'.U j) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (lbPow L n) (lbPow (L'.pull f) m)).U (idx f m n i j) :=
  inf_of x (wchart_of x L (𝟙 X) i (by simpa using hi))
    (wchart_of x (L'.pull f) (𝟙 X) _ (wchart_of x L' f j hj))
end GlobalTheory.PullHermitian
