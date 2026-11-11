-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_hasDerivAt_time
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:37.515621+00:00
-- url     : https://prove2.me/submissions/cd67342c-f309-43e7-b70a-1c73bd918d43

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

lemma heat_hasDerivAt_time_oai {t : ℝ} (ht : 0 < t) (z : V) :
    HasDerivAt (fun s => heat s z) ((-2/t+‖z‖^2/(4*t^2))*heat t z) t := by
  have hc : HasDerivAt (fun s : ℝ => 4*Real.pi*s) (4*Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4*Real.pi)
  have hi := (hc.inv (by positivity)).pow 2
  have hd := (hasDerivAt_const t (-‖z‖^2)).div
    ((hasDerivAt_id t).const_mul 4) (by positivity)
  have h := hi.mul hd.exp
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [heat, Pi.inv_apply, Pi.pow_apply, Pi.div_apply, Pi.mul_apply, id_eq]
  field_simp [ne_of_gt ht, Real.pi_ne_zero]
  ring_nf
  field_simp [ne_of_gt ht, Real.pi_ne_zero]

end TamingCompatibility.GeometricHilbert.FlatHeat

end

end OAI
end

theorem solution : type_of% @OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_hasDerivAt_time_oai := @OAI.TamingCompatibility.GeometricHilbert.FlatHeat.heat_hasDerivAt_time_oai
