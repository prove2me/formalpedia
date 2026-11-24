-- Prove2me | solution 1 for GlobalTheory.Harm.sum_filter_lt_eq_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:19.710801+00:00
-- url     : https://prove2.me/submissions/47bf0607-d963-4098-950c-336a64b0b89b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg

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
theorem _root_.solution {m : ℕ} (f : Fin m → ℤ) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), f k =
      ∑ j ∈ range i, if h : j < m then f ⟨j, h⟩ else 0 := by
  rw [Finset.sum_filter]
  have hfin := Fin.sum_univ_eq_sum_range
    (fun j => if j < i then (if h : j < m then f ⟨j, h⟩ else 0) else 0) m
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin
  rw [hfin, ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact hj.2
  · intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hj hj'
    have hjm : ¬ j < m := fun hjm => hj' hjm hj
    simp [hjm]
end _root_.GlobalTheory.Harm
end GlobalTheory.Harm
