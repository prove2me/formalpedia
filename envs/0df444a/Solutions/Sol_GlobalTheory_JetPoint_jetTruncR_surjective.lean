-- Prove2me | solution 1 for GlobalTheory.JetPoint.jetTruncR_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:10.100889+00:00
-- url     : https://prove2.me/submissions/15e69567-621d-4f4f-a90a-5ad461451b58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetPointsOfIsLieBasis

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetPoint
open GlobalTheory.SqZero
variable {R : Type} [CommRing R]
namespace GlobalTheory.JetPoint
theorem _root_.solution (κ : Type) (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩
end GlobalTheory.JetPoint
