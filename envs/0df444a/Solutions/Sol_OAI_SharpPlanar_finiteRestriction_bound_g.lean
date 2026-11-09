-- Prove2me | solution 1 for OAI.SharpPlanar.finiteRestriction_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:34:42.337198+00:00
-- url     : https://prove2.me/submissions/f52e033a-e1b5-4730-8994-1b4575876f44

import Mathlib
import Definitions.Def_OAIQ098G009
import Theorems.Thm_OAI_SharpPlanar_X_summable_g
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
lemma X_norm_scalar (x : X) : ‖x‖ = ∑' i : Node × Bool, |x i| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one,Real.rpow_one,one_div_one,Real.norm_eq_abs]
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
include he in
lemma finiteRestriction_bound_g_oai (x : X) : ‖finiteRestrictionLinear e x‖ ≤ 1*‖x‖ := by
  rw [l1Finite_norm_g,X_norm_scalar,one_mul]
  change (∑ i, |x (e i)|) ≤ _
  simpa only [tsum_fintype, Function.comp_apply] using tsum_comp_le_tsum_of_inj (X_summable_g x) (fun _ => abs_nonneg _) he
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteRestriction_bound_g_oai.{u_1} := @OAI.SharpPlanar.finiteRestriction_bound_g_oai.{u_1}
