-- Prove2me | solution 1 for GlobalTheory.JetPoint.ker_jetTruncR_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:56.734805+00:00
-- url     : https://prove2.me/submissions/7bc6a8d4-fead-4ca8-be87-f954663c7d63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetPointsOfIsLieBasis
import Theorems.Thm_GlobalTheory_JetPoint_jetAug_comp_jetTruncR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


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
theorem _root_.solution (κ : Type) (m : ℕ) :
    IsNilpotent (RingHom.ker (jetTruncR R κ m)) := by
  have hle : RingHom.ker (jetTruncR R κ m) ≤ RingHom.ker (jetAug R κ (m + 1)) := by
    intro a ha
    have ha' : jetTruncR R κ m a = 0 := ha
    change jetAug R κ (m + 1) a = 0
    rw [← jetAug_comp_jetTruncR, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← ker_jetAug_pow (R := R) κ (m + 1)]
  exact Ideal.pow_right_mono hle _
end GlobalTheory.JetPoint
