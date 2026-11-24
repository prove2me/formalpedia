-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_contains
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:44:23.202084+00:00
-- url     : https://prove2.me/submissions/51606650-5db9-4cfd-b5b1-2da80e320761

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ind_pos
import Theorems.Thm_GlobalTheory_RandomTops_ind_neg
import Theorems.Thm_GlobalTheory_RandomTops_ind_congr
import Theorems.Thm_GlobalTheory_RandomTops_ex_congr
import Theorems.Thm_GlobalTheory_RandomTops_ex_restrict

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
theorem _root_.solution {Q B : Finset ℕ} (hQ : Q ⊆ B) :
    ex δ B (fun T => ind (Q ⊆ T)) = δ ^ Q.card := by
  have e : ex δ B (fun T => ind (Q ⊆ T)) = ex δ B (fun T => ind (Q ⊆ T ∩ Q)) :=
    ex_congr fun T _ => ind_congr (by simp [subset_inter_iff])
  rw [e, ex_restrict hQ (fun T => ind (Q ⊆ T))]
  unfold ex
  rw [sum_eq_single Q]
  · beta_reduce
    rw [ind_pos subset_rfl]
    simp
  · intro T hT hne
    beta_reduce
    rw [ind_neg, mul_zero]
    exact fun h => hne (subset_antisymm (mem_powerset.mp hT) h)
  · intro h
    exact absurd (mem_powerset_self Q) h
end GlobalTheory.RandomTops
