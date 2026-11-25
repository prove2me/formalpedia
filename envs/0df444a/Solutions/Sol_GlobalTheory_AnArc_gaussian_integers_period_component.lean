-- Prove2me | solution 1 for GlobalTheory.AnArc.gaussian_integers_period_component
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:26:08.817062+00:00
-- url     : https://prove2.me/submissions/b88f12c0-2ab1-4268-abf3-b9a6fe5c2ed4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (c τ₀ : ℂ) :
    ((gaussInt c τ₀).P0 (La.mk (A := gaussInt c τ₀) 0 0 (gaussEquiv 1))).1 (1 : ℤ) = -(c / (2 * Complex.I)) := by
  change TInt τ₀ 0 1 + ((0 : ℤ) : ℂ) -
    hermForm 1 (fun _ : Fin 1 => ((1 : ℤ) : ℂ) * c) (gaussEmb 1) / (2 * Complex.I) = _
  simp [hermForm_one]
end GlobalTheory.AnArc
