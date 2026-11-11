-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:32.115206+00:00
-- url     : https://prove2.me/submissions/7fb7d2b7-610e-4ec0-90c7-b1c7faa38a80

import Mathlib
import Definitions.Def_Q238K015
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_optimum_attained_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma connection_mono {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) (p : V) :
    connection T p ≤ connection S p := by
  simp only [connection,dite_eq_left hS,dite_eq_left (hS.mono hST)]
  exact Finset.le_inf' hS _ (fun _ hs => Finset.inf'_le _ (hST hs))
lemma cost_mono (D : Finset V) {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) :
    cost D T ≤ cost D S := Finset.sum_le_sum (fun p _ => connection_mono hS hST p)

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Produce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma mem_feasibleSets (F S : Finset V) (r : ℕ) :
    S ∈ feasibleSets F r ↔ S ⊆ F ∧ S.Nonempty ∧ S.card ≤ r := by
  simp only [feasibleSets,Finset.mem_filter,Finset.mem_powerset]
lemma optimum_le (F D S : Finset V) (r : ℕ) (hSF : S ⊆ F)
    (hS : S.Nonempty) (hSr : S.card ≤ r) : optimum F D r ≤ cost D S := by
  have hm : S ∈ feasibleSets F r := (mem_feasibleSets F S r).mpr ⟨hSF,hS,hSr⟩
  rw [optimum,dite_eq_left ⟨S,hm⟩]
  exact Finset.inf'_le _ hm
lemma optimum_attained_exact_s238_oai (F D : Finset V) (hF : F.Nonempty) (r : ℕ)
    (hr : 0 < r) (hrF : r ≤ F.card) :
    ∃ O ⊆ F, O.Nonempty ∧ O.card = r ∧ cost D O = optimum F D r := by
  obtain ⟨S,hSF,hS,hSr,hcost⟩ := optimum_attained_s238 F D hF r hr
  obtain ⟨O,hSO,hOF,hOr⟩ := Finset.exists_subsuperset_card_eq hSF hSr hrF
  refine ⟨O,hOF,hS.mono hSO,hOr,?_⟩
  exact le_antisymm ((cost_mono D hS hSO).trans_eq hcost)
    (optimum_le F D O r hOF (hS.mono hSO) hOr.le)

end MetricKMedianRecovery.LocalSearch

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_exact_s238_oai.{u_1}
