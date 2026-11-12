-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:30:36.324385+00:00
-- url     : https://prove2.me/submissions/44a566d4-c13d-4f28-b00e-3eb31e20eda9

import Mathlib
import Definitions.Def_Q238L010

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
omit [PseudoMetricSpace V] in
lemma feasibleSets_nonempty (F : Finset V) (hF : F.Nonempty) (r : ℕ) (hr : 0 < r) :
    (feasibleSets F r).Nonempty := by
  obtain ⟨i,hi⟩ := hF
  exact ⟨{i},(mem_feasibleSets F {i} r).mpr
    ⟨Finset.singleton_subset_iff.mpr hi,Finset.singleton_nonempty i,by simp only [Finset.card_singleton]; omega⟩⟩
lemma optimum_attained_s238r_oai (F D : Finset V) (hF : F.Nonempty) (r : ℕ) (hr : 0 < r) :
    ∃ O ⊆ F, O.Nonempty ∧ O.card ≤ r ∧ cost D O = optimum F D r := by
  have h := feasibleSets_nonempty F hF r hr
  obtain ⟨O,hO,hmin⟩ := Finset.exists_min_image (feasibleSets F r) (cost D) h
  have hm := (mem_feasibleSets F O r).mp hO
  refine ⟨O,hm.1,hm.2.1,hm.2.2,?_⟩
  rw [optimum,dite_eq_left h]
  exact le_antisymm (Finset.le_inf' h _ hmin) (Finset.inf'_le _ hO)

end MetricKMedianRecovery.LocalSearch

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.LocalSearch.optimum_attained_s238r_oai.{u_1}
