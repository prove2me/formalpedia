-- Prove2me | solution 1 for GlobalTheory.ThetaGroupTest.weilIs_noCharts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:14.036807+00:00
-- url     : https://prove2.me/submissions/2db241bc-cf6a-49d5-844b-e153163f3b13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaGroupTest
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.ThetaScalar
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaGroupTest
theorem _root_.solution (k : ℤ) (x y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ) : WeilIs A (noCharts A.left) k x y c :=
  fun _ => ⟨⊤, trivial,
    ⟨⟨_, ⟨fun j => (j 0).elim⟩, fun j => (j 0).elim⟩, ⟨_, ⟨fun j => (j 0).elim⟩, fun j => (j 0).elim⟩, rfl, rfl⟩,
    fun _ _ _ _ j => (j (Sum.inl 0)).elim⟩
end GlobalTheory.ThetaGroupTest
