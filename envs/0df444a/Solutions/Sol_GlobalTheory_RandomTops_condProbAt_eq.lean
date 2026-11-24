-- Prove2me | solution 1 for GlobalTheory.RandomTops.condProbAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:47:44.016208+00:00
-- url     : https://prove2.me/submissions/5a18c71d-17d4-4d94-b5f1-fe824f4e9821

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops

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
theorem _root_.solution {n i₀ : ℕ} (hi : i₀ < n) (A : Finset ℕ → Prop) :
    condProbAt n δ i₀ A = ex δ ((Finset.range n).erase i₀) (fun U => ind (A (insert i₀ U))) := by
  have hmem : i₀ ∈ range n := mem_range.mpr hi
  have hnot : i₀ ∉ (range n).erase i₀ := notMem_erase _ _
  have hcard : #((range n).erase i₀) = n - 1 := by rw [card_erase_of_mem hmem, card_range]
  unfold condProbAt ex
  conv_lhs => rw [← insert_erase hmem]
  rw [sum_powerset_insert hnot, sum_eq_zero, zero_add]
  · refine sum_congr rfl fun U hU => ?_
    have hU' : i₀ ∉ U := fun h => hnot (mem_powerset.mp hU h)
    rw [card_insert_of_notMem hU', hcard]
    unfold ind
    beta_reduce
    by_cases hA : A (insert i₀ U)
    · rw [if_pos ⟨mem_insert_self _ _, hA⟩, if_pos hA, Nat.add_sub_cancel, mul_one,
        show n - (#U + 1) = n - 1 - #U by omega]
    · rw [if_neg (fun h => hA h.2), if_neg hA, mul_zero]
  · intro T hT
    exact if_neg (fun h => hnot (mem_powerset.mp hT h.1))
end GlobalTheory.RandomTops
