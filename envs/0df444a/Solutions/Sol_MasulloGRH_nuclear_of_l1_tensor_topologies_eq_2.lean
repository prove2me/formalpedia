-- Prove2me | solution 2 for MasulloGRH.nuclear_of_l1_tensor_topologies_eq
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:12:04.460704+00:00
-- url     : https://prove2.me/submissions/9b313b75-7cc1-49c1-80ac-0f15e3008e46

import Theorems.Thm_MasulloGRH_abs_summing_of_l1_tensor_topologies_eq
import Theorems.Thm_MasulloGRH_quasinuclear_domination_of_abs_summing
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E)
    (ht : projTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) =
      epsTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1))) : IsNuclear E := by
  have hsumming := abs_summing_of_l1_tensor_topologies_eq E hE ht
  have hdomination := quasinuclear_domination_of_abs_summing E hE hsumming
  exact nuclear_of_quasinuclear_domination E hE hdomination
