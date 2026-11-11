-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:36.614264+00:00
-- url     : https://prove2.me/submissions/f970e517-a144-4d44-bbb3-b3082e87d96d

import Mathlib
import Definitions.Def_OAIQ239Tc003

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_FlatHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FlatHeat
open _root_.MeasureTheory Set
open scoped RealInnerProductSpace ContDiff

lemma heat_contDiff_oai (t : ℝ) : ContDiff ℝ ∞ (heat t) := by
  exact contDiff_const.mul (((contDiff_id.norm_sq (𝕜 := ℝ)).neg.div_const (4*t)).exp)

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_contDiff_oai := @OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_contDiff_oai
