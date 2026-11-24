-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:11:17.017689+00:00
-- url     : https://prove2.me/submissions/5b04a684-6a70-4790-b9e2-0d74703ad849

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ex_congr
import Theorems.Thm_GlobalTheory_RandomTops_ex_mul_left
import Theorems.Thm_GlobalTheory_RandomTops_ex_union

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
theorem _root_.solution {A S : Finset ℕ} (hA : A ⊆ S) (f g : Finset ℕ → ℝ) :
    ex δ S (fun T => f (T ∩ A) * g (T \ A)) = ex δ A f * ex δ (S \ A) g := by
  have hd : Disjoint A (S \ A) := disjoint_sdiff
  conv_lhs => rw [← union_sdiff_of_subset hA]
  rw [ex_union hd]
  have e : ∀ T ⊆ A, ex δ (S \ A) (fun U => f ((T ∪ U) ∩ A) * g ((T ∪ U) \ A)) =
      f T * ex δ (S \ A) g := by
    intro T hT
    rw [← ex_mul_left]
    refine ex_congr fun U hU => ?_
    have e1 : (T ∪ U) ∩ A = T := by
      ext x
      have h1 := @hT x
      have h2 := @hU x
      simp only [mem_inter, mem_union, mem_sdiff] at *
      tauto
    have e2 : (T ∪ U) \ A = U := by
      ext x
      have h1 := @hT x
      have h2 := @hU x
      simp only [mem_union, mem_sdiff] at *
      tauto
    rw [e1, e2]
  rw [ex_congr e]
  have := ex_mul_left (δ := δ) A (ex δ (S \ A) g) f
  rw [mul_comm, ← this]
  congr 1
  funext T
  ring
end GlobalTheory.RandomTops
