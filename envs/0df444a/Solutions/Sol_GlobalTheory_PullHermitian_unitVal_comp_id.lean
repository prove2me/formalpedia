-- Prove2me | solution 1 for GlobalTheory.PullHermitian.unitVal_comp_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:07.41233+00:00
-- url     : https://prove2.me/submissions/1d9ed95c-d488-4adb-b1ce-74956d889bf6

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
theorem _root_.solution {U : X.Opens} (h : ⊤ ≤ (x ≫ 𝟙 X) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    unitVal (x ≫ 𝟙 X) h f = unitVal x h' f := by
  simp only [Category.comp_id]
end GlobalTheory.PullHermitian
