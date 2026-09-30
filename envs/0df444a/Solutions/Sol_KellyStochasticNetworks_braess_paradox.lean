-- Prove2me | solution 1 for KellyStochasticNetworks.braess_paradox
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:33.722613+00:00
-- url     : https://prove2.me/submissions/9a801d86-bdc7-416d-98ea-f7aacc1963e9

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

end KellyStochasticNetworks

open KellyStochasticNetworks
theorem solution :
    (IsWardropEquilibrium braessIncidenceA (fun _ => (0 : Fin 1)) braessDelayA
        (fun _ => 6) ![3, 3]
      ∧ ∀ r : Fin 2, (∑ j, braessDelayA j (linkFlow braessIncidenceA ![3, 3] j)
            * braessIncidenceA j r) = 83)
  ∧ (IsWardropEquilibrium braessIncidenceB (fun _ => (0 : Fin 1)) braessDelayB
        (fun _ => 6) ![2, 2, 2]
      ∧ ∀ r : Fin 3, (∑ j, braessDelayB j (linkFlow braessIncidenceB ![2, 2, 2] j)
            * braessIncidenceB j r) = 92) := by
  have hσA : ∀ σ : Fin 1, σ = 0 := fun σ => Subsingleton.elim σ 0
  have hσB : ∀ σ : Fin 1, σ = 0 := fun σ => Subsingleton.elim σ 0
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  · intro r; fin_cases r <;> norm_num
  · intro σ; rw [hσA σ]; norm_num [Fin.sum_univ_two]
  · intro r r' _ _
    fin_cases r <;> fin_cases r' <;>
      simp [linkFlow, braessIncidenceA, braessDelayA, Fin.sum_univ_four, Fin.sum_univ_two] <;>
      norm_num
  · intro r; fin_cases r <;>
      simp [linkFlow, braessIncidenceA, braessDelayA, Fin.sum_univ_four, Fin.sum_univ_two] <;>
      norm_num
  · intro r; fin_cases r <;> norm_num
  · intro σ; rw [hσB σ]; simp [Fin.sum_univ_three]; norm_num
  · intro r r' _ _
    fin_cases r <;> fin_cases r' <;>
      simp [linkFlow, braessIncidenceB, braessDelayB, Fin.sum_univ_succ] <;>
      norm_num
  · intro r; fin_cases r <;>
      simp [linkFlow, braessIncidenceB, braessDelayB, Fin.sum_univ_succ] <;>
      norm_num

