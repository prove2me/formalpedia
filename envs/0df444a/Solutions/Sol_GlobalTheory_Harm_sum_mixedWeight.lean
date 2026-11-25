-- Prove2me | solution 1 for GlobalTheory.Harm.sum_mixedWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:47.929955+00:00
-- url     : https://prove2.me/submissions/46f110ee-501c-4dea-84cc-dae037e37a7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
import Theorems.Thm_GlobalTheory_Harm_mixedWeight_apply
import Theorems.Thm_GlobalTheory_Harm_sum_dite_lt
import Theorems.Thm_GlobalTheory_Harm_sum_dite_rev_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset
namespace GlobalTheory.Harm
namespace _root_.GlobalTheory.Harm
theorem _root_.solution {m p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ k, _root_.GlobalTheory.Harm.mixedWeight m a b k = ∑ i, (a i : ℤ) - ∑ i, (b i : ℤ) := by
  have h1 := _root_.GlobalTheory.Harm.sum_dite_lt (m := m) (by omega : p ≤ m)
    (fun i => (a i : ℤ))
  have h2 := _root_.GlobalTheory.Harm.sum_dite_rev_lt (m := m) (by omega : q ≤ m)
    (fun i => (b i : ℤ))
  beta_reduce at h1 h2
  simp only [_root_.GlobalTheory.Harm.mixedWeight_apply, Finset.sum_sub_distrib]
  rw [h1, h2]
end _root_.GlobalTheory.Harm
end GlobalTheory.Harm
