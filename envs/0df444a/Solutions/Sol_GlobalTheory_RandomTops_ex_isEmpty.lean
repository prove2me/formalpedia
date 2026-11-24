-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:45.487385+00:00
-- url     : https://prove2.me/submissions/2eba9f0a-943d-4029-abac-e0c33c3494fd

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution (C : Finset ℕ) : ex δ C (fun V => ind (V = ∅)) = (1 - δ) ^ C.card := by
  unfold ex
  rw [sum_eq_single ∅]
  · simp [ind]
  · intro T _ hne
    beta_reduce
    rw [ind_neg hne, mul_zero]
  · intro h
    exact absurd (empty_mem_powerset C) h
end GlobalTheory.RandomTops
