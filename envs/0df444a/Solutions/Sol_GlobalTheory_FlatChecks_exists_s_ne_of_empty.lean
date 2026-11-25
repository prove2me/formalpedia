-- Prove2me | solution 1 for GlobalTheory.FlatChecks.exists_s_ne_of_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:42:58.696057+00:00
-- url     : https://prove2.me/submissions/94c5c2e1-0b03-4b60-8826-63a80a504a8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_CoordDifferentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FlatChecks
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FlatChecks
theorem _root_.solution (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (h : Fl.δ = 0) :
    ∀ x ∈ X.dom, ∃ k, Fl.s k x ≠ 0 := by
  intro x hx
  by_contra hn
  push Not at hn
  obtain ⟨j, -⟩ := (Fl.S_eq x hx).1 hn
  exact absurd j.2 (by omega)
end GlobalTheory.FlatChecks
