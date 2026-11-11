-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:28.664198+00:00
-- url     : https://prove2.me/submissions/5dcd82ac-9fe1-4ee9-9f2f-7c276be1dd7f

import Mathlib
import Definitions.Def_Q238K015
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_local_five_approx_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_AllBadCostBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

lemma local_combined_cost_bound_s238_oai (F D S O : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hlocal : WidthLocalMin F D S 5) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) :
    (∑ p ∈ D, (connection S p + connection O p)) ≤ 6*cost D O := by
  have h := local_five_approx_s238 F D S O hS hO hSF hlocal hOF hcard
  rw [Finset.sum_add_distrib]
  change cost D S+cost D O ≤ 6*cost D O
  linarith

end MetricKMedianRecovery.LocalSearch

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.LocalSearch.local_combined_cost_bound_s238_oai.{u_1}
