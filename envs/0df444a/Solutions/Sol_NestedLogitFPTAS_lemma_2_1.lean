-- Prove2me | solution 1 for NestedLogitFPTAS.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:03:33.611209+00:00
-- url     : https://prove2.me/submissions/cdf942cc-8c6a-4f15-a2f6-7ecec9075bb7

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Neighbourhood

open NestedLogitFPTAS in
theorem solution {n M : ℕ} (I : Instance n M) (hI : I.Standing) {Sstar S : Finset (Fin n)}
    (hSstar : I.Feasible Sstar) (hS : I.IsDualOptimal Sstar S) :
    I.Feasible S ∧ I.R S = I.R Sstar := by
  have hfilt : Finset.univ.filter (fun m : Fin M => 1 ≤ m.val + 1 ∧ m.val + 1 ≤ M) =
      Finset.univ := Finset.filter_true_of_mem (fun m _ => ⟨by omega, by omega⟩)
  have hR : ∀ T, I.R T = I.rhoRange 1 M T / (I.w0 + I.omegaRange 1 M T) := by
    intro T
    unfold Instance.R Instance.nu Instance.rhoRange Instance.omegaRange
    simp only [hfilt]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  refine ⟨le_trans (hS.2 Sstar ⟨rfl, rfl⟩) hSstar, ?_⟩
  rw [hR, hR, hS.1.1, hS.1.2]
