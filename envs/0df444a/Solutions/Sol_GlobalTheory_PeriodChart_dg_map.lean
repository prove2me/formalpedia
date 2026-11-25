-- Prove2me | solution 1 for GlobalTheory.PeriodChart.dg_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:10.351207+00:00
-- url     : https://prove2.me/submissions/c17b8f64-1cd2-4cfe-9057-e567dc3ccf4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) :
    (dg ty a).map (starRingEnd ℂ) = dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by
  unfold dg
  rw [Matrix.diagonal_map (map_zero _)]
  rfl
end GlobalTheory.PeriodChart
