-- Prove2me | solution 1 for OAI.SharpPlanar.finiteRestriction_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T04:37:34.425821+00:00
-- url     : https://prove2.me/submissions/4687668e-6148-44c8-910a-bfcd97231c98

import Mathlib
import Definitions.Def_OAIQ098E009
import Theorems.Thm_OAI_SharpPlanar_X_summable_e
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_e

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
lemma finiteRestriction_bound_e_oai (x : X) : ‖finiteRestrictionLinear e x‖ ≤ 1*‖x‖ := by
  rw [l1Finite_norm_e,X_norm_scalar,one_mul]
  change (∑ i, |x (e i)|) ≤ _
  simpa only [tsum_fintype, Function.comp_apply] using tsum_comp_le_tsum_of_inj (X_summable_e x) (fun _ => abs_nonneg _) he
end
end SharpPlanar

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpPlanar.finiteRestriction_bound_e_oai.{u_1} := @OAI.SharpPlanar.finiteRestriction_bound_e_oai.{u_1}
