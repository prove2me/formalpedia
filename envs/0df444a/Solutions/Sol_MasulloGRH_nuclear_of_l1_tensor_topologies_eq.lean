-- Prove2me | solution 1 for MasulloGRH.nuclear_of_l1_tensor_topologies_eq
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:11:13.2191+00:00
-- url     : https://prove2.me/submissions/d9194bbf-73f1-434d-9e1f-027c1b24508e

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_abs_summing_of_l1_tensor_topologies_eq
import Theorems.Thm_MasulloGRH_quasinuclear_domination_of_abs_summing
import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (ht : projTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1)) =
      epsTensorTopology E (ULift.{u} (lp (fun _ : ℕ => ℂ) 1))) : IsNuclear E :=
  nuclear_of_quasinuclear_domination E hE
    (quasinuclear_domination_of_abs_summing E hE
      (abs_summing_of_l1_tensor_topologies_eq E hE ht))
