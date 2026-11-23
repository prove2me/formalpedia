-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Int.norm_dbl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:42.87687+00:00
-- url     : https://prove2.me/submissions/214fdd13-c97b-48cc-ac41-ff99d3aa4991

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
namespace GlobalTheory.Ex.NumD.Int
theorem _root_.solution (h : N.Int q) (x : N.A) : ‖((dbl N.θ N.σ x : Cˣ) : C)‖ = 1 := by
  rw [dbl, Units.val_div_eq_div_val, norm_div, h.θ, h.σ, div_one]
end GlobalTheory.Ex.NumD.Int
