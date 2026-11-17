-- Prove2me | solution 1 for N25.level25_indices
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:50.534902+00:00
-- url     : https://prove2.me/submissions/bed3fe57-c47f-4369-bc95-e4c970975f0c

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_gammaH_index
import Theorems.Thm_N25_level25_subgroup_index
import Theorems.Thm_N25_level25_gamma0_index

set_option autoImplicit false

namespace N25

/-- Indices of the two level-25 subgroups in the integral modular group. -/
theorem _root_.solution :
    (CohCarrier.GammaH 25 H25).index = 150 ∧
    (CongruenceSubgroup.Gamma0 25).index = 30 := by
  have h0 : (CongruenceSubgroup.Gamma0 25).index = 30 := by
    exact level25_gamma0_index
  constructor
  · rw [level25_gammaH_index, level25_subgroup_index, h0]
  · exact h0

end N25
