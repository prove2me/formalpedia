-- Prove2me | solution 1 for GlobalTheory.Harm.casimir_value_mixedWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:37.889617+00:00
-- url     : https://prove2.me/submissions/d1a9d353-6653-449a-8527-df0eb424ab05

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
    ∑ k : Fin m, _root_.GlobalTheory.Harm.mixedWeight m a b k * (_root_.GlobalTheory.Harm.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (∑ i : Fin p, (a i : ℤ) * (a i + p - 1 - 2 * (i : ℕ)) + ((m : ℤ) - p) * ∑ i, (a i : ℤ)) +
      (∑ i : Fin q, (b i : ℤ) * (b i + q - 1 - 2 * (i : ℕ)) + ((m : ℤ) - q) * ∑ i, (b i : ℤ)) := by
  have hp : p ≤ m := by omega
  have hq : q ≤ m := by omega
  have h1 := _root_.GlobalTheory.Harm.sum_dite_lt hp
    (fun i : Fin p => (a i : ℤ) * (a i + m - 1 - 2 * (i : ℕ)))
  have h2 := _root_.GlobalTheory.Harm.sum_dite_rev_lt hq
    (fun j : Fin q => (b j : ℤ) * (b j + m - 1 - 2 * (j : ℕ)))
  beta_reduce at h1 h2
  simp only [Fin.val_mk] at h1 h2
  have hpt : ∀ k : Fin m, _root_.GlobalTheory.Harm.mixedWeight m a b k *
        (_root_.GlobalTheory.Harm.mixedWeight m a b k + m - 1 - 2 * (k : ℕ)) =
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) * (a ⟨k, h⟩ + m - 1 - 2 * (k : ℕ)) else 0) +
      (if h : m - 1 - (k : ℕ) < q then
        (b ⟨m - 1 - k, h⟩ : ℤ) * (b ⟨m - 1 - k, h⟩ + m - 1 - 2 * (m - 1 - (k : ℕ) : ℕ))
        else 0) := by
    intro k
    have hk := k.isLt
    have hc : ((m - 1 - (k : ℕ) : ℕ) : ℤ) = (m : ℤ) - 1 - (k : ℕ) := by omega
    rw [_root_.GlobalTheory.Harm.mixedWeight_apply]
    split_ifs <;> first | omega | (rw [hc]; ring) | ring
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, h1, h2,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring
end _root_.GlobalTheory.Harm
end GlobalTheory.Harm
