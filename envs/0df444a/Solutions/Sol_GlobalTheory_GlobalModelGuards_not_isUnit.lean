-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.not_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:33:04.046379+00:00
-- url     : https://prove2.me/submissions/d45c49fb-8425-4a0c-86d5-1cdf42a9cc6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.GlobalModelGuards
theorem _root_.solution {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (p : ℕ) (hW : (p : ℂ) ∈ W.nonunits) :
    ¬ IsUnit (p : c.V W) := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvW : ((v : c.F) : ℂ) ∈ W := v.2
  have h1 : (p : ℂ) * ((v : c.F) : ℂ) = 1 := by
    have := congrArg (fun z : c.V W => ((z : c.F) : ℂ)) hv
    simpa using this
  rw [ValuationSubring.mem_nonunits_iff] at hW
  have h2 := (W.valuation_le_one_iff _).2 hvW
  have h3 := congrArg W.valuation h1
  rw [map_mul, map_one] at h3
  have : W.valuation p * W.valuation ((v : c.F) : ℂ) < 1 := mul_lt_one_of_lt_of_le hW h2
  exact this.ne h3
end GlobalTheory.GlobalModelGuards
